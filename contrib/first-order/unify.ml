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
open Names
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

let is_head_meta t=match kind_of_term t with Meta _->true | _ ->false

let value i t=
  let add x y=
    if x<0 then y else if y<0 then x else x+y in
  let tref=mkMeta i in
  let rec vaux term=
    if term=tref then 0 else 
      let f v t=add v (vaux t) in
      let vr=fold_constr f (-1) term in
	if vr<0 then -1 else vr+1 in
    vaux t
	  
type instance=
    Real of constr*int (* instance*valeur heuristique*)
  | Phantom of constr (* domaine de quantification *)
 	  
let unif_atoms i dom t1 t2=
  if is_head_meta t1 || is_head_meta t2  then None else
    try 
      let t=List.assoc i (unif t1 t2) in 
	if is_ground t then Some (Real(t,value i t1))
	else if is_head_meta t then Some (Phantom dom)
	else None
    with
	UFAIL(_,_) ->None
      | Not_found ->Some (Phantom dom)
      
let compare_instance inst1 inst2=
	match inst1,inst2 with
	    Phantom(d1),Phantom(d2)->
	      (OrderedConstr.compare d1 d2)
	  | Real(c1,n1),Real(c2,n2)->
	      ((-) =? OrderedConstr.compare) n2 n1 c1 c2
	  | Phantom(_),_-> 1
	  | _,_-> -1

module OrderedRightInstance=
struct 
  type t = constr*int
  let compare (c1,n1) (c2,n2) = ((-) =? OrderedConstr.compare) n2 n1 c1 c2
end

module OrderedLeftInstance=
struct
  type t=instance * Libnames.global_reference
  let compare (inst1,id1) (inst2,id2)=
    (compare_instance =? Pervasives.compare) inst1 inst2 id1 id2
    (* we want a __decreasing__ total order *)
end
  
module RIS=Set.Make(OrderedRightInstance)
module LIS=Set.Make(OrderedLeftInstance)
  
(* le premier argument est une sous formule a instancier *)

let match_atom_with_latoms i dom (pol,atom) latoms accu=
  if pol then 
    let f latom accu=
      match unif_atoms i dom atom latom with
	  None->accu
	| Some (Phantom _) ->(true,snd accu)
	| Some (Real(t,i)) ->(false,RIS.add (t,i) (snd accu)) in
      List.fold_right f latoms accu
  else accu 

let match_atom_with_hyp_atoms i dom (pol,atom) lf accu=
  let f (b,hatom) accu=
    if b=pol then accu else
      match unif_atoms i dom atom hatom with
	  None->accu
	| Some (Phantom _) ->(true,snd accu)
	| Some (Real(t,i))->(false,RIS.add (t,i) (snd accu)) in
    List.fold_right f lf.atoms accu

let match_atom_with_goal i dom (pol,atom) glatoms accu=
  let f (b,glatom) accu=
    if b=pol then accu else
      match unif_atoms i dom atom glatom with
	  None->accu
	| Some (Phantom _) ->(true,snd accu)
	| Some (Real(t,i)) ->(false,RIS.add (t,i) (snd accu)) in
    List.fold_right f glatoms accu

let give_right_instances i dom ratoms seq=
  let f ratom accu=
    let accu1= match_atom_with_goal i dom ratom ratoms accu in
    let accu2=
      match_atom_with_latoms i dom ratom seq.latoms accu1 in
      HP.fold (match_atom_with_hyp_atoms i dom ratom) seq.redexes accu2 in
  let (b,accu0)=List.fold_right f ratoms (false,RIS.empty) in
    if b & RIS.is_empty accu0 then 
      None
    else
      Some (RIS.elements accu0)

(*left*) 
	  
let match_named_atom_with_latoms id i dom (pol,atom) latoms accu=
  if pol then 
    let f latom accu=
      match unif_atoms i dom atom latom with
	  None->accu
	| Some (Phantom _) ->(true,snd accu)
	| Some inst ->(false,LIS.add (inst,id) (snd accu)) in
      List.fold_right f latoms accu
  else accu 

let match_named_atom_with_hyp_atoms id i dom (pol,atom) lf accu=
  let f (b,hatom) accu=
    if b=pol then accu else
      match unif_atoms i dom atom hatom with
	  None->accu
	| Some (Phantom _) ->(true,snd accu)
	| Some inst->(false,LIS.add (inst,id) (snd accu)) in
    List.fold_right f lf.atoms accu

let match_named_atom_with_goal id i dom (pol,atom) gl accu=
  match gl with 
      Atomic t->
	if pol then accu else
	  (match unif_atoms i dom atom t with
	       None->accu
	     | Some (Phantom _) ->(true,snd accu)
	     | Some inst ->(false,LIS.add (inst,id) (snd accu)))
    | Complex (_,_,glatoms)->
	let f (b,glatom) accu=
	  if b=pol then accu else
	    match unif_atoms i dom atom glatom with
		None->accu
	      | Some (Phantom _) ->(true,snd accu)
	      | Some inst ->(false,LIS.add (inst,id) (snd accu)) in
	  List.fold_right f glatoms accu

let match_one_forall_hyp seq lf accu=
  match lf.pat with 
      Lforall(i,dom)->
	let f latom accu=
	  let accu1=match_named_atom_with_goal lf.id i dom latom seq.gl accu in
	  let accu2=
	    match_named_atom_with_latoms lf.id i dom latom seq.latoms accu1 in
	    HP.fold (match_named_atom_with_hyp_atoms lf.id i dom latom) 
	      seq.redexes accu2 in
	let (b,accu0)=List.fold_right f lf.atoms (false,LIS.empty) in
	  if b & LIS.is_empty accu0 then 
	    LIS.add (Phantom dom,lf.id) accu
	  else
	    LIS.union accu0 accu
    | _ ->anomaly "can't happen" 

let give_left_instances lfh seq=
  LIS.elements (List.fold_right (match_one_forall_hyp seq) lfh LIS.empty)

(* TODO: match with goal *)
