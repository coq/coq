(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

(* This file is the interface between the c-c algorithm and Coq *)

open Evd
open Proof_type
open Names
open Libnames
open Nameops
open Term
open Tacmach
open Tactics
open Tacticals
open Ccalgo
open Tacinterp
open Ccproof
open Pp
open Util
open Format

exception Not_an_eq

let fail()=raise Not_an_eq
    
let constr_of_string s () =
  constr_of_reference (Nametab.locate (qualid_of_string s))

let eq2eqT_theo = constr_of_string "Coq.Logic.Eqdep_dec.eq2eqT"
let eqT2eq_theo = constr_of_string "Coq.Logic.Eqdep_dec.eqT2eq"
let congr_theo = constr_of_string "Coq.cc.CC.Congr_nodep"
let congr_dep_theo = constr_of_string "Coq.cc.CC.Congr_dep"

let fresh_id1=id_of_string "eq1" and fresh_id2=id_of_string "eq2"
    
let t_make_app=(Array.fold_left (fun s t->Appli (s,t)))

(* decompose member of equality in an applicative format *)

let rec decompose_term t=
  match kind_of_term t with
    App (f,args)->let targs=Array.map decompose_term args in
    (t_make_app (Symb f) targs)
  | _->(Symb t)

(* decompose equality in members and type *)
	
let eq_type_of_term term=
  match kind_of_term term with
      App (f,args)->
	(try 
	   let ref = reference_of_constr f in
	     if (ref=Coqlib.glob_eq || ref=Coqlib.glob_eqT) && 
	       (Array.length args)=3 
	     then (args.(0),args.(1),args.(2)) 
	     else fail()
	 with
	     Not_found -> fail ())
    | _ ->fail ()

(* read an equality *)
	  
let read_eq term=
  let (_,t1,t2)=eq_type_of_term term in 
    ((decompose_term t1),(decompose_term t2))

(* rebuild a term from applicative format *)
    
let rec make_term=function
    Symb s->s
  | Appli (s1,s2)->make_app [(make_term s2)] s1
and make_app l=function
    Symb s->mkApp (s,(Array.of_list l))
  | Appli (s1,s2)->make_app ((make_term s2)::l) s1

(* store all equalities from the context *)
	
let rec read_hyps=function
    []->[]
  | (id,_,e)::hyps->let q=(read_hyps hyps) in
      try (id,(read_eq e))::q with Not_an_eq -> q

(* build a problem ( i.e. read the goal as an equality ) *)
	
let make_prb gl=
  let concl=gl.evar_concl in
  let hyps=gl.evar_hyps in
  (read_hyps hyps),(read_eq concl)

(* apply tac, followed (or not) by aplication of theorem theo *)

let st_wrap theo tac= 
  tclORELSE tac (tclTHEN (apply theo) tac)

(* generate an adhoc tactic following the proof tree  *)

let rec proof_tac uf axioms=function
    Ax id->(fun gl->(st_wrap (eq2eqT_theo ()) (exact_check (mkVar id)) gl))
  | Refl t->reflexivity
  | Trans (p1,p2)->let t=(make_term (snd (type_proof uf axioms p1))) in
      (tclTHENS (transitivity t) 
	 [(proof_tac uf axioms p1);(proof_tac uf axioms p2)])
  | Sym p->tclTHEN symmetry (proof_tac uf axioms p)
  | Congr (p1,p2)->
      (fun gl->
	 let (s1,t1)=(type_proof uf axioms p1) and
	   (s2,t2)=(type_proof uf axioms p2) in
         let ts1=(make_term s1) and tt1=(make_term t1) 
	and ts2=(make_term s2) and tt2=(make_term t2) in
      let typ1=pf_type_of gl ts1 and typ2=pf_type_of gl ts2 in
      let (typb,_,_)=(eq_type_of_term gl.it.evar_concl) in
      let act=mkApp ((congr_theo ()),[|typ2;typb;ts1;tt1;ts2;tt2|]) in
      tclORELSE 
	(tclTHENS 
	   (apply act)	 
	   [(proof_tac uf axioms p1);(proof_tac uf axioms p2)])		
	   (tclTHEN
	      (let p=mkLambda(destProd typ1) in
	      let acdt=mkApp((congr_dep_theo ()),[|typ2;p;ts1;tt1;ts2|]) in 
	      apply acdt) (proof_tac uf axioms p1))
	gl)

(* wrap everything *)
	
let cc_tactic gl_sg=
  Library.check_required_library ["Coq";"cc";"CC"];
  let gl=gl_sg.it in
  let prb=try make_prb gl with Not_an_eq ->
    errorlabstrm  "CC" [< str "Couldn't match goal with an equality" >] in
  match (cc_proof prb) with
    None->errorlabstrm  "CC" [< str "CC couldn't solve goal" >] 
  | Some (p,uf,axioms)->let tac=proof_tac uf axioms p in
    (tclORELSE (st_wrap (eqT2eq_theo ()) tac)
       (fun _->errorlabstrm  "CC" 
	  [< str "CC doesn't know how to handle dependent equality." >]) gl_sg)

(* Tactic registration *)
      
TACTIC EXTEND CC
 [ "CC" ] -> [ cc_tactic ]
END










   
