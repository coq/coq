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
	
let rec up_path uf i l=
  let (cl,_,_)=(Hashtbl.find uf i) in
  match cl with 
    UF.Eqto(j,t)->up_path uf j (((i,j),t)::l)
  | UF.Rep(_,_)->l
	
let rec min_path=function 
    ([],l2)->([],l2)
  | (l1,[])->(l1,[])
  | (((c1,t1)::q1),((c2,t2)::q2)) as cpl->
      if c1=c2 then 
	min_path (q1,q2) 
      else 
	cpl
	  
let pcongr=function
    ((Refl t1),(Refl t2))->Refl (Appli (t1,t2))
  | (p1,p2) -> Congr (p1,p2)

let rec ptrans=function
    ((Refl _),p)->p
  | (p,(Refl _))->p
  | (Trans(p1,p2),p3)->ptrans(p1,ptrans (p2,p3))
  | (Congr(p1,p2),Congr(p3,p4))->pcongr(ptrans(p1,p3),ptrans(p2,p4))
  | (Congr(p1,p2),Trans(Congr(p3,p4),p5))->
	ptrans(pcongr(ptrans(p1,p3),ptrans(p2,p4)),p5)
  | (p1,p2)->Trans (p1,p2)
	
let rec psym=function
    Refl p->Refl p
  | Sym p->p
  | Ax s-> Sym(Ax s)
  | Trans (p1,p2)-> ptrans ((psym p2),(psym p1))
  | Congr (p1,p2)-> pcongr ((psym p1),(psym p2))
	
let pcongr=function
    ((Refl t1),(Refl t2))->Refl (Appli (t1,t2))
  | (p1,p2) -> Congr (p1,p2)
	
let build_proof ((a,m):UF.t) i j=
  let rec equal_proof i j=
    let (li,lj)=min_path ((up_path m i []),(up_path m j [])) in
    ptrans ((path_proof i li),(psym (path_proof j lj)))
  and arrow_proof ((i,j),t)=
    let (i0,j0,t0)=t in
    let pi=(equal_proof i i0) in
    let pj=psym (equal_proof j j0) in
    let pij=
      match t0 with 
	UF.Ax s->Ax s
      | UF.Congr->(congr_proof i0 j0)	
    in  ptrans(ptrans (pi,pij),pj)
  and path_proof i=function
      []->let (_,_,t)=Hashtbl.find m i in Refl t
    | (((_,j),_) as x)::q->ptrans ((path_proof j q),(arrow_proof x))
  and congr_proof i j=
    let (_,vi,_)=(Hashtbl.find m i) and (_,vj,_)=(Hashtbl.find m j) in   
    match (vi,vj) with
      ((UF.Node(i1,i2)),(UF.Node(j1,j2)))->
	pcongr ((equal_proof i1 j1),(equal_proof i2 j2))
    | _ -> failwith "congr_proof: couldn't find subterms"
  in
  (equal_proof i j)
    
let rec type_proof uf axioms p=
  match p with
    Ax s->List.assoc s axioms
  | Refl t->(t,t)
  | Trans (p1,p2)->
      let (s1,t1)=type_proof uf axioms p1 
      and (t2,s2)=type_proof uf axioms p2 in
      if t1=t2 then (s1,s2) else failwith "invalid transitivity"
  | Sym p->let (t1,t2)=type_proof uf axioms p in (t2,t1)
  | Congr (p1,p2)->
      let (i1,j1)=(type_proof uf axioms p1)
      and (i2,j2)=(type_proof uf axioms p2) in
      ((Appli (i1,i2)),(Appli (j1,j2)))
	
let cc_proof (axioms,(v,w))=
  let syms=Hashtbl.create init_size in
  let uf=make_uf syms axioms in
  let i1=(UF.add v uf syms) in
  let i2=(UF.add w uf syms) in
  cc uf;
  if (UF.find uf i1)=(UF.find uf i2) then 
    let p=(build_proof uf i1 i2) in
    (if (v,w)=(type_proof uf axioms p) then Some (p,uf,axioms) 
    else failwith "Proof check failed !!")
  else
    None;;

    



