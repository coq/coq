(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* This file uses the (non-compressed) union-find structure to generate *) 
(* proof-trees that will be transformed into proof-terms in cctac.ml4   *)

open Util
open Names
open Term
open Ccalgo
  
type proof=
    Ax of constr
  | SymAx of constr
  | Refl of term
  | Trans of proof*proof
  | Congr of proof*proof
  | Inject of proof*constructor*int*int 
		  
let pcongr=function
    Refl t1, Refl t2 -> Refl (Appli (t1,t2))
  | p1, p2 -> Congr (p1,p2)

let rec ptrans=function
    Refl _, p ->p
  | p, Refl _ ->p
  | Trans(p1,p2), p3 ->ptrans(p1,ptrans (p2,p3))
  | Congr(p1,p2), Congr(p3,p4) ->pcongr(ptrans(p1,p3),ptrans(p2,p4))
  | Congr(p1,p2), Trans(Congr(p3,p4),p5) ->
      ptrans(pcongr(ptrans(p1,p3),ptrans(p2,p4)),p5)
  | p1, p2 ->Trans (p1,p2)
	
let rec psym=function
    Refl p->Refl p
  | SymAx s->Ax s
  | Ax s-> SymAx s
  | Inject (p,c,n,a)-> Inject (psym p,c,n,a)
  | Trans (p1,p2)-> ptrans (psym p2,psym p1)
  | Congr (p1,p2)-> pcongr (psym p1,psym p2)
	
let pcongr=function
    Refl t1, Refl t2 ->Refl (Appli (t1,t2))
  | p1, p2 -> Congr (p1,p2)

let build_proof uf=
  
  let rec equal_proof i j=
    if i=j then Refl (term uf i) else 
      let (li,lj)=join_path uf i j in
	ptrans (path_proof i li,psym (path_proof j lj))
  
  and edge_proof ((i,j),eq)=
    let pi=equal_proof i eq.lhs in
    let pj=psym (equal_proof j eq.rhs) in
    let pij=
      match eq.rule with 
	  Axiom (s,reversed)->if reversed then SymAx s else Ax s
	| Congruence ->congr_proof eq.lhs eq.rhs
	| Injection (ti,ipac,tj,jpac,k) ->
	    let p=ind_proof ti ipac tj jpac in
	    let cinfo= get_constructor_info uf ipac.cnode in
	      Inject(p,cinfo.ci_constr,cinfo.ci_nhyps,k)	
    in  ptrans(ptrans (pi,pij),pj)

  and constr_proof i t ipac=
    if ipac.args=[] then
      equal_proof i t
    else
      let npac=tail_pac ipac in
      let (j,arg)=subterms uf t in
      let targ=term uf arg in
      let rj=find uf j in
      let u=find_pac uf rj npac in
      let p=constr_proof j u npac in
	ptrans (equal_proof i t, pcongr (p,Refl targ))

  and path_proof i=function
      [] -> Refl (term uf i)
    | x::q->ptrans (path_proof (snd (fst x)) q,edge_proof x)
  
  and congr_proof i j=
    let (i1,i2) = subterms uf i
    and (j1,j2) = subterms uf j in   
      pcongr (equal_proof i1 j1, equal_proof i2 j2)
	
  and ind_proof i ipac j jpac=
    let p=equal_proof i j 
    and p1=constr_proof i i ipac 
    and p2=constr_proof j j jpac in
      ptrans(psym p1,ptrans(p,p2))
  in
    function
	`Prove (i,j) -> equal_proof i j
      | `Discr (i,ci,j,cj)-> ind_proof i ci j cj

let rec nth_arg t n=
  match t with 
      Appli (t1,t2)-> 
	if n>0 then 
	  nth_arg t1 (n-1)
	else t2
    | _ -> anomaly "nth_arg: not enough args"

let rec type_proof axioms p=
  match p with
      Ax s->Hashtbl.find axioms s
    | SymAx s-> let (t1,t2)=Hashtbl.find axioms s in (t2,t1)
    | Refl t-> t,t
    | Trans (p1,p2)->
	let (s1,t1)=type_proof axioms p1 
	and (t2,s2)=type_proof axioms p2 in
	  if t1=t2 then (s1,s2) else anomaly "invalid cc transitivity"
    | Congr (p1,p2)->
	let (i1,j1)=type_proof axioms p1
	and (i2,j2)=type_proof axioms p2 in
	  Appli (i1,i2),Appli (j1,j2)
    | Inject (p,c,n,a)->
	let (ti,tj)=type_proof axioms p in
	  nth_arg ti (n-a),nth_arg tj (n-a)

