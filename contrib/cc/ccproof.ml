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

open Util
open Names
open Ccalgo
  
type proof=
    Ax of identifier
  | SymAx of identifier
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

let pid (s:string) (p:proof)=p
	
let build_proof uf i j=
  
  let rec equal_proof i j=
    if i=j then Refl (UF.term uf i) else 
      let (li,lj)=UF.join_path uf i j in
	ptrans (path_proof i li,psym (path_proof j lj))
  
  and edge_proof ((i,j),eq)=
    let pi=equal_proof i eq.lhs in
    let pj=psym (equal_proof j eq.rhs) in
    let pij=
      match eq.rule with 
	  Axiom s->Ax s
	| Congruence ->congr_proof eq.lhs eq.rhs
	| Injection (ti,tj,c,a) ->
	    let p=equal_proof ti tj in
	    let arity=UF.pac_arity uf (UF.find uf ti) (c,0) in
	    let p1=constr_proof ti ti c 0 arity
	    and p2=constr_proof tj tj c 0 arity  in
	      match UF.term uf c with
		  Constructor (cstr,nargs,nhyps) -> 
		    Inject(ptrans(psym p1,ptrans(p,p2)),cstr,nhyps,a)
		| _ -> anomaly "injection on non-constructor terms" 
    in  ptrans(ptrans (pi,pij),pj)

  and constr_proof i j c n a=
       if n<a then 
	 let nj=UF.mem_node_pac uf j (c,n) in
	 let (ni,arg)=UF.subterms uf j in 
	 let p=constr_proof ni nj c (n+1) a in
	 let targ=UF.term uf arg in 
	   ptrans (equal_proof i j, pcongr (p,Refl targ))
       else equal_proof i j

  and path_proof i=function
      [] -> Refl (UF.term uf i)
    | x::q->ptrans (path_proof j q,edge_proof x)
  
  and congr_proof i j=
    let (i1,i2) = UF.subterms uf i
    and (j1,j2) = UF.subterms uf j in   
      pcongr (equal_proof i1 j1, equal_proof i2 j2)
  
  in
    equal_proof i j

let rec nth_arg t n=
  match t with 
      Appli (t1,t2)-> 
	if n>0 then 
	  nth_arg t1 (n-1)
	else t2
    | _ -> anomaly "nth_arg: not enough args"

let rec type_proof axioms p=
  match p with
      Ax s->List.assoc s axioms
    | SymAx s-> let (t1,t2)=List.assoc s axioms in (t2,t1)
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

exception Wrong_proof of proof

let cc_proof (axioms,(v,w))=
  let uf=make_uf axioms in
  let i1=UF.add uf v in
  let i2=UF.add uf w in
  cc uf;
  if UF.find uf i1=UF.find uf i2 then 
    let prf=build_proof uf i1 i2 in
      if (v,w)=type_proof axioms prf then Some (prf,uf,axioms) 
      else anomaly "Oops !! Wrong equality proof generated"
  else
    None

    



