(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util
open Names
open Term
open Tacmach
open Tactics
open Tacticals
open Termops
open Reductionops
open Declarations
open Formula
open Sequent
open Unify
open Libnames

type hptac= Sequent.t -> (Sequent.t -> tactic) -> counter -> tactic

type lhptac= global_reference -> hptac
  
let wrap n b seq tacrec metagen gls=
  let nc=pf_hyps gls in
  let rec aux i nc=
    if i<=0 then seq else 
      match nc with
	  []->anomaly "Not the expected number of hyps"
	| (id,_,typ)::q-> 
	    let gr=VarRef id in 
	    (add_left (gr,typ) (aux (i-1) q) true metagen) in
  let seq1=
    if b then
      (change_right (pf_concl gls) (aux n nc) metagen)
    else
      (aux n nc) in
    tacrec seq1 gls

let clear_global=function
    VarRef id->clear [id]
  | _->tclIDTAC
      
let axiom_tac t seq=
  try exact_no_check (constr_of_reference (find_left t seq)) 
  with Not_found->tclFAIL 0 "No axiom link" 

let and_tac seq tacrec metagen=
  tclTHEN simplest_split (wrap 0 true seq tacrec metagen)

let left_and_tac ind id seq tacrec metagen=
  let n=(construct_nhyps ind).(0) in  
    tclTHENLIST 
      [simplest_elim (constr_of_reference id);
       clear_global id; 
       tclDO n intro;
       wrap n false seq tacrec metagen]

let or_tac seq tacrec metagen=
  any_constructor (Some (tclSOLVE [wrap 0 true seq tacrec metagen]))

let left_or_tac ind id seq tacrec metagen=
  let v=construct_nhyps ind in  
  let f n=
    tclTHENLIST
      [clear_global id;
       tclDO n intro;
       wrap n false seq tacrec metagen] in
    tclTHENSV
      (simplest_elim (constr_of_reference id))
      (Array.map f v)

let forall_tac seq tacrec metagen=
  tclTHEN intro (wrap 0 true seq tacrec metagen)

let left_forall_tac i dom atoms id seq tacrec metagen=
  let insts=find_instances i atoms seq in
    if insts=[] then 
      tclTHENS (cut dom) 
	[tclTHENLIST
	   [intro;
	    (fun gls->generalize 
	       [mkApp(constr_of_reference id,[|mkVar (Tacmach.pf_nth_hyp_id gls 1)|])] gls);
	    intro;
	    tclSOLVE [wrap 1 false seq tacrec metagen]]
	;tclIDTAC]
    else
      let tac t=
	tclTHENLIST 
	  [generalize [mkApp(constr_of_reference id,[|t|])];
	   intro; 
	   tclSOLVE [wrap 1 false seq tacrec metagen]] in
	tclFIRST (List.map tac insts)
	  
let arrow_tac seq tacrec metagen=
  tclTHEN intro (wrap 1 true seq tacrec metagen)
    
let exists_tac i dom atoms seq tacrec metagen=
  let insts=find_instances i atoms seq in
    if insts=[] then 
      tclTHENS (cut dom) 
	[tclTHENLIST
	   [intro;
	    (fun gls->
	       split (Rawterm.ImplicitBindings 
			[mkVar (Tacmach.pf_nth_hyp_id gls 1)]) gls);
	       tclSOLVE [wrap 0 false seq tacrec metagen]]
	    ;tclIDTAC]
	 else
	   let tac t=
	     tclTHEN (split (Rawterm.ImplicitBindings [t]))
	       (tclSOLVE [wrap 0 true seq tacrec metagen]) in
	     tclFIRST (List.map tac insts)
	       
let left_exists_tac id seq tacrec metagen=
  tclTHENLIST
    [simplest_elim (constr_of_reference id);
     clear_global id;
     tclDO 2 intro;
     (wrap 1 false seq tacrec metagen)]

let ll_arrow_tac a b c id seq tacrec metagen=
  let cc=mkProd(Anonymous,a,(lift 1 b)) in
  let d=mkLambda (Anonymous,b,
		  mkApp ((constr_of_reference id),
			 [|mkLambda (Anonymous,(lift 1 a),(mkRel 2))|])) in
    tclTHENS (cut c)
      [tclTHENLIST
	 [intro;
	  clear_global id;
	  wrap 1 false seq tacrec metagen];
       tclTHENS (cut cc) 
         [exact_no_check (constr_of_reference id); 
	  tclTHENLIST 
	    [generalize [d];
	     intro;
	     clear_global id;
	     tclSOLVE [wrap 1 true seq tacrec metagen]]]]

let ll_atom_tac a id seq tacrec metagen=
  try 
    tclTHENLIST
      [generalize [mkApp(constr_of_reference id,
			 [|constr_of_reference (find_left a seq)|])];
       clear_global id;
       intro;
       wrap 1 false seq tacrec metagen] 
  with Not_found->tclFAIL 0 "No link" 

let ll_false_tac id seq tacrec metagen=
  tclTHEN (clear_global id) (wrap 0 false seq tacrec metagen)

let left_false_tac id=
  simplest_elim (constr_of_reference id)

(*We use this function for and, or, exists*)

let ll_ind_tac ind largs id seq tacrec metagen gl= 
  (try
     let rcs=ind_hyps ind largs in
     let vargs=Array.of_list largs in
	     (* construire le terme  H->B, le generaliser etc *)   
     let myterm i=
       let rc=rcs.(i) in
       let p=List.length rc in
       let cstr=mkApp ((mkConstruct (ind,(i+1))),vargs) in
       let vars=Array.init p (fun j->mkRel (p-j)) in
       let capply=mkApp ((lift p cstr),vars) in
       let head=mkApp ((lift p (constr_of_reference id)),[|capply|]) in
	 Sign.it_mkLambda_or_LetIn head rc in
       let lp=Array.length rcs in
       let newhyps=List.map myterm (interval 0 (lp-1)) in
	 tclTHENLIST 
	   [generalize newhyps;
	    clear_global id;
	    tclDO lp intro;
	    wrap lp false seq tacrec metagen]
   with Dependent_Inductive | Invalid_argument _ ->tclFAIL 0 "") gl

let ll_forall_tac prod id seq tacrec metagen=
  tclTHENS (cut prod)
    [tclTHENLIST
       [(fun gls->generalize 
	   [mkApp(constr_of_reference id,
		  [|mkVar (Tacmach.pf_nth_hyp_id gls 1)|])] gls);
	clear_global id;
	intro;
	tclSOLVE [wrap 1 false seq tacrec metagen]];
       tclSOLVE [wrap 0 true seq tacrec metagen]]

