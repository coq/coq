(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Constr
open EConstr
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

let pop t = Vars.lift (-1) t
let subst_meta subst t =
  let subst = List.map (fun (m, c) -> (m, EConstr.Unsafe.to_constr c)) subst in
  EConstr.of_constr (subst_meta subst (EConstr.Unsafe.to_constr t))

let unif evd t1 t2=
  let bige=Queue.create ()
  and sigma=ref [] in
  let bind i t=
    sigma:=(i,t)::
      (List.map (function (n,tn)->(n,subst_meta [i,t] tn)) !sigma) in
  let rec head_reduce t=
    (* forbids non-sigma-normal meta in head position*)
    match EConstr.kind evd t with
	Meta i->
	  (try
	     head_reduce (Int.List.assoc i !sigma)
	   with Not_found->t)
      | _->t in
    Queue.add (t1,t2) bige;
    try while true do
      let t1,t2=Queue.take bige in
      let nt1=head_reduce (whd_betaiotazeta evd t1)
      and nt2=head_reduce (whd_betaiotazeta evd t2) in
	match (EConstr.kind evd nt1),(EConstr.kind evd nt2) with
	    Meta i,Meta j->
	      if not (Int.equal i j) then
		if i<j then bind j nt1
		else bind i nt2
	  | Meta i,_ ->
	      let t=subst_meta !sigma nt2 in
		if Int.Set.is_empty (free_rels evd t) &&
                  not (occur_metavariable evd i t) then
		    bind i t else raise (UFAIL(nt1,nt2))
	  | _,Meta i ->
	      let t=subst_meta !sigma nt1 in
		if Int.Set.is_empty (free_rels evd t) &&
                  not (occur_metavariable evd i t) then
		    bind i t else raise (UFAIL(nt1,nt2))
	  | Cast(_,_,_),_->Queue.add (strip_outer_cast evd nt1,nt2) bige
 	  | _,Cast(_,_,_)->Queue.add (nt1,strip_outer_cast evd nt2) bige
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
	  | _->if not (eq_constr_nounivs evd nt1 nt2) then raise (UFAIL (nt1,nt2))
    done;
      assert false
	(* this place is unreachable but needed for the sake of typing *)
    with Queue.Empty-> !sigma

let value evd i t=
  let add x y=
    if x<0 then y else if y<0 then x else x+y in
  let rec vaux term=
    if isMeta evd term && Int.equal (destMeta evd term) i then 0 else
      let f v t=add v (vaux t) in
      let vr=EConstr.fold evd f (-1) term in
	if vr<0 then -1 else vr+1 in
    vaux t

type instance=
    Real of (int*constr)*int
  | Phantom of constr

let mk_rel_inst evd t=
  let new_rel=ref 1 in
  let rel_env=ref [] in
  let rec renum_rec d t=
    match EConstr.kind evd t with
	Meta n->
	  (try
	     mkRel (d+(Int.List.assoc n !rel_env))
	   with Not_found->
	     let m= !new_rel in
	       incr new_rel;
	       rel_env:=(n,m) :: !rel_env;
	       mkRel (m+d))
      | _ -> EConstr.map_with_binders evd succ renum_rec d t
  in
  let nt=renum_rec 0 t in (!new_rel - 1,nt)

let unif_atoms evd i dom t1 t2=
  try
    let t=Int.List.assoc i (unif evd t1 t2) in
      if isMeta evd t then Some (Phantom dom)
      else Some (Real(mk_rel_inst evd t,value evd i t1))
  with
      UFAIL(_,_) ->None
    | Not_found ->Some (Phantom dom)

let renum_metas_from k n t= (* requires n = max (free_rels t) *)
  let l=List.init n (fun i->mkMeta (k+i)) in
    substl l t

let more_general evd (m1,t1) (m2,t2)=
  let mt1=renum_metas_from 0 m1 t1
  and mt2=renum_metas_from m1 m2 t2 in
    try
      let sigma=unif evd mt1 mt2 in
      let p (n,t)= n<m1 || isMeta evd t in
	List.for_all p sigma
    with UFAIL(_,_)->false
