(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Util
open Formula 
open Sequent
open Tacmach
open Term
open Termops
open Reductionops

exception UFAIL of constr*constr

let unif t1 t2= (* Martelli-Montanari style *)
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
	     head_reduce (List.assoc i !sigma) 
	   with Not_found->t)
      | _->t in 
    Queue.add (t1,t2) bige;
    try while true do
      let t1,t2=Queue.take bige in
      let nt1=head_reduce (whd_betaiotazeta t1) 
      and nt2=head_reduce (whd_betaiotazeta t2) in
	match (kind_of_term nt1),(kind_of_term nt2) with
	    Meta i,Meta j-> 
	      if i<>j then 
		if i<j then bind j nt1
		else bind i nt2
	  | Meta i,_ ->
	      let t=subst_meta !sigma nt2 in
		if Intset.is_empty (free_rels t) && 
		  not (occur_term (mkMeta i) t) then
		    bind i t else raise (UFAIL(nt1,nt2))
	  | _,Meta i -> 
	      let t=subst_meta !sigma nt1 in
		if Intset.is_empty (free_rels t) && 
		  not (occur_term (mkMeta i) t) then
		    bind i t else raise (UFAIL(nt1,nt2))
	  | Cast(_,_),_->Queue.add (strip_outer_cast nt1,nt2) bige
 	  | _,Cast(_,_)->Queue.add (nt1,strip_outer_cast nt2) bige 
	  | (Prod(_,a,b),Prod(_,c,d))|(Lambda(_,a,b),Lambda(_,c,d))->
	      Queue.add (a,c) bige;Queue.add (pop b,pop d) bige
	  | Case (_,pa,ca,va),Case (_,pb,cb,vb)->
	      Queue.add (pa,pb) bige;
	      Queue.add (ca,cb) bige;
	      let l=Array.length va in
		if l<>(Array.length vb) then 
		  raise (UFAIL (nt1,nt2))
		else 
		  for i=0 to l-1 do
		    Queue.add (va.(i),vb.(i)) bige
		  done	  
	  | App(ha,va),App(hb,vb)->
	      Queue.add (ha,hb) bige;
	      let l=Array.length va in
		if l<>(Array.length vb) then 
		  raise (UFAIL (nt1,nt2))
		else 
		  for i=0 to l-1 do
		    Queue.add (va.(i),vb.(i)) bige
		  done
	  | _->if not (eq_constr nt1 nt2) then raise (UFAIL (nt1,nt2))
    done;
      assert false 
	(* this place is unreachable but needed for the sake of typing *)
    with Queue.Empty-> !sigma
      
(* collect tries finds ground instantiations for Meta i*)
let is_ground t=(Clenv.collect_metas t)=[]

let collect i l=
  try
    let t=List.assoc i l in 
      if is_ground t then Some t else None
  with Not_found->None

let unif_atoms_for_meta i (b1,t1) (b2,t2)=
  if b1=b2 then None else
    try 
      collect i (unif t1 t2) 
    with UFAIL(_,_) ->None
    
module OrderedConstr=
struct
  type t=constr
  let compare=Pervasives.compare
end

module CS=Set.Make(OrderedConstr)

let match_atom_list i atom l=
  let f atom2 accu=
    match unif_atoms_for_meta i atom atom2 with
	None-> accu
      | Some t-> CS.add t accu in
    List.fold_right f l CS.empty

let match_lists i l1 l2=
  let f atom accu=
    CS.union (match_atom_list i atom l2) accu in
    List.fold_right f l1 CS.empty
      
let find_instances i l seq=
  let match_hyp f accu=
    CS.union (if f.internal then match_lists i l f.atoms else CS.empty) accu in
  let match_atom t nam accu=
    CS.union (match_atom_list i (false,t) l) accu in
  let s1=
    match seq.gl with 
	Atomic t->(match_atom_list i (true,t) l)
      | Complex(_,l1)->(match_lists i l l1) in
  let s2=CM.fold match_atom seq.hatoms s1 in
  let s3=HP.fold match_hyp seq.hyps s2 in
    CS.fold (fun x l->x::l) s3 []

