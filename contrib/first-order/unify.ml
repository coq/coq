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
open Pattern
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
    Real of (constr*int) (* instance*valeur heuristique*)
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

let make_goal_atoms seq=
  match seq.gl with
      Atomic t->{negative=[];positive=[t]}
    | Complex (_,_,l)->l 

let make_left_atoms seq=
    {negative=seq.latoms;positive=[]}

let do_sequent setref triv add mkelt seq i dom atoms=
  let flag=ref true in
  let phref=ref triv in
  let do_atoms a1 a2 =
    let do_pair t1 t2 = 
      match unif_atoms i dom t1 t2 with
	  None->()
	| Some (Phantom _) ->phref:=true
	| Some c ->flag:=false;setref:=add (mkelt c) !setref in
      List.iter (fun t->List.iter (do_pair t) a2.negative) a1.positive;
      List.iter (fun t->List.iter (do_pair t) a2.positive) a1.negative in
    HP.iter (fun lf->do_atoms atoms lf.atoms) seq.redexes;
    do_atoms atoms (make_left_atoms seq);
    do_atoms atoms (make_goal_atoms seq);
    !flag && !phref 
 
let give_right_instances i dom triv atoms seq=
  let setref=ref RIS.empty in
  let inj=function
       Real c->c
     | _->anomaly "can't happen" in
  if do_sequent setref triv RIS.add inj seq i dom atoms then
    None
  else
    Some (RIS.elements !setref)

let match_one_forall_hyp setref seq lf=
  match lf.pat with 
      Lforall(i,dom,triv)->
	let inj x=(x,lf.id) in
	  if do_sequent setref triv LIS.add inj seq i dom lf.atoms then
	    setref:=LIS.add ((Phantom dom),lf.id) !setref 
    | _ ->anomaly "can't happen" 

let give_left_instances lfh seq=
  let setref=ref LIS.empty in
    List.iter (match_one_forall_hyp setref seq) lfh;
    LIS.elements !setref

