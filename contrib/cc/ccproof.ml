(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(* This file uses the (non-compressed) union-find structure to generate *) 
(* proof-trees that will be transformed into proof-terms in cctac.ml4   *)

open Names
open Ccalgo
  
type proof=
    Ax of identifier
  | Refl of term
  | Trans of proof*proof
  | Sym of proof
  | Congr of proof*proof
		  
let pcongr=function
    Refl t1, Refl t2 ->Refl (Appli (t1,t2))
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
  | Sym p->p
  | Ax s-> Sym(Ax s)
  | Trans (p1,p2)-> ptrans (psym p2,psym p1)
  | Congr (p1,p2)-> pcongr (psym p1,psym p2)
	
let pcongr=function
    Refl t1, Refl t2 ->Refl (Appli (t1,t2))
  | p1, p2 -> Congr (p1,p2)
	
let build_proof uf i j=
  
  let rec equal_proof i j=
    let (li,lj)=UF.join_path uf i j in
      ptrans (path_proof i li,psym (path_proof j lj))
  
  and edge_proof ((i,j),t)=
    let pi=equal_proof i t.lhs in
    let pj=psym (equal_proof j t.rhs) in
    let pij=
      match t.rule with 
	  Axiom s->Ax s
	| Congruence->congr_proof t.lhs t.rhs
    in  ptrans(ptrans (pi,pij),pj)
  
  and path_proof i=function
      [] -> let t=UF.term uf i in Refl t
    | x::q->ptrans (path_proof j q,edge_proof x)
  
  and congr_proof i j=
    let (i1,i2) = UF.subterms uf i
    and (j1,j2) = UF.subterms uf j in   
      pcongr (equal_proof i1 j1, equal_proof i2 j2)
  
  in
    equal_proof i j

let rec type_proof axioms p=
  match p with
    Ax s->List.assoc s axioms
  | Refl t-> t,t
  | Trans (p1,p2)->
      let (s1,t1)=type_proof axioms p1 
      and (t2,s2)=type_proof axioms p2 in
      if t1=t2 then (s1,s2) else failwith "invalid transitivity"
  | Sym p->let (t1,t2)=type_proof axioms p in (t2,t1)
  | Congr (p1,p2)->
      let (i1,j1)=type_proof axioms p1
      and (i2,j2)=type_proof axioms p2 in
      Appli (i1,i2),Appli (j1,j2)
	
let cc_proof (axioms,(v,w))=
  let uf=make_uf axioms in
  let i1=UF.add v uf in
  let i2=UF.add w uf in
  cc uf;
  if UF.find uf i1=UF.find uf i2 then 
    let prf=build_proof uf i1 i2 in
      if (v,w)=type_proof axioms prf then Some (prf,uf,axioms) 
      else failwith "Proof check failed !!"
  else
    None;;

    



