(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Term
open Vars
open Termops
open Reductionops

exception UFAIL of constr*constr

(*
   RIGID-only Martelli-Montanari style unification for CLOSED terms
   I repeat : t1 and t2 must NOT have ANY free deBruijn
   sigma is kept normal with respect to itself but is lazily applied
   to the equation set. Raises UFAIL with a pair of  terms
*)

let unif t1 t2=
  let bige=Queue.create ()
  and sigma=ref [] in
  let bind i t=
    sigma:=(i,t)::
      (List.map (function (n,tn)->(n,subst_meta [i,t] tn)) !sigma) in
  let rec head_reduce t=
    (* forbids non-sigma-normal meta in head position*)
    match kind_of_term t with
	Meta i->
	  (try
	     head_reduce (Int.List.assoc i !sigma)
	   with Not_found->t)
      | _->t in
    Queue.add (t1,t2) bige;
    try while true do
      let t1,t2=Queue.take bige in
      let nt1=head_reduce (whd_betaiotazeta Evd.empty t1)
      and nt2=head_reduce (whd_betaiotazeta Evd.empty t2) in
	match (kind_of_term nt1),(kind_of_term nt2) with
	    Meta i,Meta j->
	      if not (Int.equal i j) then
		if i<j then bind j nt1
		else bind i nt2
	  | Meta i,_ ->
	      let t=subst_meta !sigma nt2 in
		if Int.Set.is_empty (free_rels t) &&
		  not (occur_term (mkMeta i) t) then
		    bind i t else raise (UFAIL(nt1,nt2))
	  | _,Meta i ->
	      let t=subst_meta !sigma nt1 in
		if Int.Set.is_empty (free_rels t) &&
		  not (occur_term (mkMeta i) t) then
		    bind i t else raise (UFAIL(nt1,nt2))
	  | Cast(_,_,_),_->Queue.add (strip_outer_cast nt1,nt2) bige
 	  | _,Cast(_,_,_)->Queue.add (nt1,strip_outer_cast nt2) bige
	  | (Prod(_,a,b),Prod(_,c,d))|(Lambda(_,a,b),Lambda(_,c,d))->
	      Queue.add (a,c) bige;Queue.add (pop b,pop d) bige
	  | Case (_,pa,ca,va),Case (_,pb,cb,vb)->
	      Queue.add (pa,pb) bige;
	      Queue.add (ca,cb) bige;
	      let l=Array.length va in
		if not (Int.equal l (Array.length vb)) then
		  raise (UFAIL (nt1,nt2))
		else
		  for i=0 to l-1 do
		    Queue.add (va.(i),vb.(i)) bige
		  done
	  | App(ha,va),App(hb,vb)->
	      Queue.add (ha,hb) bige;
	      let l=Array.length va in
		if not (Int.equal l (Array.length vb)) then
		  raise (UFAIL (nt1,nt2))
		else
		  for i=0 to l-1 do
		    Queue.add (va.(i),vb.(i)) bige
		  done
	  | _->if not (eq_constr_nounivs nt1 nt2) then raise (UFAIL (nt1,nt2))
    done;
      assert false
	(* this place is unreachable but needed for the sake of typing *)
    with Queue.Empty-> !sigma

let value i t=
  let add x y=
    if x<0 then y else if y<0 then x else x+y in
  let rec vaux term=
    if isMeta term && Int.equal (destMeta term) i then 0 else
      let f v t=add v (vaux t) in
      let vr=fold_constr f (-1) term in
	if vr<0 then -1 else vr+1 in
    vaux t

type instance=
    Real of (int*constr)*int
  | Phantom of constr

let mk_rel_inst t=
  let new_rel=ref 1 in
  let rel_env=ref [] in
  let rec renum_rec d t=
    match kind_of_term t with
	Meta n->
	  (try
	     mkRel (d+(Int.List.assoc n !rel_env))
	   with Not_found->
	     let m= !new_rel in
	       incr new_rel;
	       rel_env:=(n,m) :: !rel_env;
	       mkRel (m+d))
      | _ -> map_constr_with_binders succ renum_rec d t
  in
  let nt=renum_rec 0 t in (!new_rel - 1,nt)

let unif_atoms i dom t1 t2=
  try
    let t=Int.List.assoc i (unif t1 t2) in
      if isMeta t then Some (Phantom dom)
      else Some (Real(mk_rel_inst t,value i t1))
  with
      UFAIL(_,_) ->None
    | Not_found ->Some (Phantom dom)

let renum_metas_from k n t= (* requires n = max (free_rels t) *)
  let l=List.init n (fun i->mkMeta (k+i)) in
    substl l t

let more_general (m1,t1) (m2,t2)=
  let mt1=renum_metas_from 0 m1 t1
  and mt2=renum_metas_from m1 m2 t2 in
    try
      let sigma=unif mt1 mt2 in
      let p (n,t)= n<m1 || isMeta t in
	List.for_all p sigma
    with UFAIL(_,_)->false
