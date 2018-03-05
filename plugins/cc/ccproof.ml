(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file uses the (non-compressed) union-find structure to generate *)
(* proof-trees that will be transformed into proof-terms in cctac.ml4   *)

open CErrors
open Constr
open Ccalgo
open Pp

type rule=
    Ax of constr
  | SymAx of constr
  | Refl of term
  | Trans of proof*proof
  | Congr of proof*proof
  | Inject of proof*pconstructor*int*int
and proof =
    {p_lhs:term;p_rhs:term;p_rule:rule}

let prefl t = {p_lhs=t;p_rhs=t;p_rule=Refl t}

let pcongr p1 p2 =
  match p1.p_rule,p2.p_rule with
    Refl t1, Refl t2 -> prefl (Appli (t1,t2))
  | _, _ ->
      {p_lhs=Appli (p1.p_lhs,p2.p_lhs);
       p_rhs=Appli (p1.p_rhs,p2.p_rhs);
       p_rule=Congr (p1,p2)}

let rec ptrans p1 p3=
  match p1.p_rule,p3.p_rule with
      Refl _, _ ->p3
    | _, Refl _ ->p1
    | Trans(p1,p2), _ ->ptrans p1 (ptrans p2 p3)
    | Congr(p1,p2), Congr(p3,p4) ->pcongr (ptrans p1 p3) (ptrans p2 p4)
    | Congr(p1,p2), Trans({p_rule=Congr(p3,p4)},p5) ->
	ptrans (pcongr (ptrans p1 p3) (ptrans p2 p4)) p5
  | _, _ ->
      if term_equal p1.p_rhs p3.p_lhs then
	{p_lhs=p1.p_lhs;
	 p_rhs=p3.p_rhs;
	 p_rule=Trans (p1,p3)}
      else anomaly (Pp.str "invalid cc transitivity.")

let rec psym p =
  match p.p_rule with
      Refl _ -> p
    | SymAx s ->
	{p_lhs=p.p_rhs;
	 p_rhs=p.p_lhs;
	 p_rule=Ax s}
    | Ax s->
	{p_lhs=p.p_rhs;
	 p_rhs=p.p_lhs;
	 p_rule=SymAx s}
  | Inject (p0,c,n,a)->
      {p_lhs=p.p_rhs;
       p_rhs=p.p_lhs;
       p_rule=Inject (psym p0,c,n,a)}
  | Trans (p1,p2)-> ptrans (psym p2) (psym p1)
  | Congr (p1,p2)-> pcongr (psym p1) (psym p2)

let pax axioms s =
  let l,r = Constrhash.find axioms s in
    {p_lhs=l;
     p_rhs=r;
     p_rule=Ax s}

let psymax axioms s =
  let l,r = Constrhash.find axioms s in
    {p_lhs=r;
     p_rhs=l;
     p_rule=SymAx s}

let rec nth_arg t n=
  match t with
      Appli (t1,t2)->
	if n>0 then
	  nth_arg t1 (n-1)
	else t2
    | _ -> anomaly ~label:"nth_arg" (Pp.str "not enough args.")

let pinject p c n a =
  {p_lhs=nth_arg p.p_lhs (n-a);
   p_rhs=nth_arg p.p_rhs (n-a);
   p_rule=Inject(p,c,n,a)}

let rec equal_proof uf i j=
  debug (fun () -> str "equal_proof " ++ pr_idx_term uf i ++ brk (1,20) ++ pr_idx_term uf j);
  if i=j then prefl (term uf i) else
    let (li,lj)=join_path uf i j in
    ptrans (path_proof uf i li) (psym (path_proof uf j lj))
      
and edge_proof uf ((i,j),eq)=
  debug (fun () -> str "edge_proof " ++ pr_idx_term uf i ++ brk (1,20) ++ pr_idx_term uf j);
  let pi=equal_proof uf i eq.lhs in
  let pj=psym (equal_proof uf j eq.rhs) in
  let pij=
    match eq.rule with
      Axiom (s,reversed)->
	if reversed then psymax (axioms uf) s
	else pax (axioms uf) s
    | Congruence ->congr_proof uf eq.lhs eq.rhs
    | Injection (ti,ipac,tj,jpac,k) -> (* pi_k ipac = p_k jpac *) 
      let p=ind_proof uf ti ipac tj jpac in
      let cinfo= get_constructor_info uf ipac.cnode in
      pinject p cinfo.ci_constr cinfo.ci_nhyps k in  
  ptrans (ptrans pi pij) pj
  
and constr_proof uf i ipac=
  debug (fun () -> str "constr_proof " ++ pr_idx_term uf i ++ brk (1,20));
  let t=find_oldest_pac uf i ipac in
  let eq_it=equal_proof uf i t in
  if ipac.args=[] then
    eq_it
  else
    let fipac=tail_pac ipac in
    let (fi,arg)=subterms uf t in
    let targ=term uf arg in
    let p=constr_proof uf fi fipac in
    ptrans eq_it (pcongr p (prefl targ))
      
and path_proof uf i l=
  debug (fun () -> str "path_proof " ++ pr_idx_term uf i ++ brk (1,20) ++ str "{" ++
	   (prlist_with_sep (fun () -> str ",") (fun ((_,j),_) -> int j) l) ++ str "}");
  match l with
  | [] -> prefl (term uf i)
  | x::q->ptrans (path_proof uf (snd (fst x)) q) (edge_proof uf x)
    
and congr_proof uf i j=
  debug (fun () -> str "congr_proof " ++ pr_idx_term uf i ++ brk (1,20) ++ pr_idx_term uf j);
  let (i1,i2) = subterms uf i
  and (j1,j2) = subterms uf j in
  pcongr (equal_proof uf i1 j1) (equal_proof uf i2 j2)
    
and ind_proof uf i ipac j jpac=
   debug (fun () -> str "ind_proof " ++ pr_idx_term uf i ++ brk (1,20) ++ pr_idx_term uf j);
  let p=equal_proof uf i j
  and p1=constr_proof uf i ipac
  and p2=constr_proof uf j jpac in
  ptrans (psym p1) (ptrans p p2)

let build_proof uf=
  function
  | `Prove (i,j) -> equal_proof uf i j
  | `Discr (i,ci,j,cj)-> ind_proof uf i ci j cj



