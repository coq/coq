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

type seqtac= (Sequent.t -> tactic) -> Sequent.t -> tactic

type lseqtac= global_reference -> seqtac

let wrap n b tacrec seq gls=
  let nc=pf_hyps gls in
  let rec aux i nc=
    if i<=0 then seq else 
      match nc with
	  []->anomaly "Not the expected number of hyps"
	| (id,_,typ)::q-> 
	    let gr=VarRef id in 
	    (add_left (gr,typ) (aux (i-1) q) true gls) in
  let seq1=
    if b then
      (change_right (pf_concl gls) (aux n nc) gls)
    else
      (aux n nc) in
    tacrec seq1 gls

let id_of_global=function
    VarRef id->id
  | _->assert false

let clear_global=function
    VarRef id->clear [id]
  | _->tclIDTAC
      
let axiom_tac t seq=
  try exact_no_check (constr_of_reference (find_left t seq)) 
  with Not_found->tclFAIL 0 "No axiom link" 

let evaluable_tac ec tacrec seq gl=
  tclTHEN
    (unfold_in_concl [[1],ec]) 
    (wrap 0 true tacrec seq) gl

let left_evaluable_tac ec id tacrec seq gl=
  tclTHENLIST
    [generalize [constr_of_reference id];
     clear_global id;
     intro;
     (fun gls->
	let nid=(Tacmach.pf_nth_hyp_id gls 1) in
	  unfold_in_hyp [[1],ec] (Tacexpr.InHypType nid) gls);
     wrap 1 false tacrec seq] gl
    
let and_tac tacrec seq=
  tclTHEN simplest_split (wrap 0 true tacrec seq)

let left_and_tac ind id tacrec seq=
  let n=(construct_nhyps ind).(0) in  
    tclTHENLIST 
      [simplest_elim (constr_of_reference id);
       clear_global id; 
       tclDO n intro;
       wrap n false tacrec seq]

let or_tac tacrec seq=
  any_constructor (Some (tclSOLVE [wrap 0 true tacrec seq]))

let left_or_tac ind id tacrec seq=
  let v=construct_nhyps ind in  
  let f n=
    tclTHENLIST
      [clear_global id;
       tclDO n intro;
       wrap n false tacrec seq] in
    tclTHENSV
      (simplest_elim (constr_of_reference id))
      (Array.map f v)

let forall_tac tacrec seq=
  tclTHEN intro (wrap 0 true tacrec seq)

let left_forall_tac i dom atoms internal id tacrec seq=
  let insts=find_instances i atoms seq in
    if insts=[] then
      if internal && not (lookup id None seq) then
	tclTHENS (cut dom) 
	  [tclTHENLIST
	     [intro;
	      (fun gls->generalize 
	       [mkApp(constr_of_reference id,
		      [|mkVar (Tacmach.pf_nth_hyp_id gls 1)|])] gls);
	      intro;
	      tclSOLVE [wrap 1 false tacrec 
			  (deepen (record id None seq))]]
	  ;tclTRY assumption]
      else tclFAIL 0 "no phantom variable for external hyp"
    else
      let tac t=
	if lookup id (Some t) seq then 
	  tclFAIL 0 "already done" 
	else
	  tclTHENLIST 
	    [generalize [mkApp(constr_of_reference id,[|t|])];
	     intro; 
	     tclSOLVE 
	       [wrap 1 false tacrec 
		  (deepen (record id (Some t) seq))]] in
	tclFIRST (List.map tac insts)
	  
let arrow_tac tacrec seq=
  tclTHEN intro (wrap 1 true tacrec seq)
    
let exists_tac i dom atoms tacrec seq=
  let insts=find_instances i atoms seq in
    if insts=[] then 
      tclTHENS (cut dom) 
	[tclTHENLIST
	   [intro;
	    (fun gls->
	       split (Rawterm.ImplicitBindings 
			[mkVar (Tacmach.pf_nth_hyp_id gls 1)]) gls);
	       tclSOLVE [wrap 0 false tacrec (deepen seq)]]
	    ;tclTRY assumption]
	 else
	   let tac t=
	     tclTHEN (split (Rawterm.ImplicitBindings [t]))
	       (tclSOLVE [wrap 0 true tacrec (deepen seq)]) in
	     tclFIRST (List.map tac insts)
	       
let left_exists_tac id tacrec seq=
  tclTHENLIST
    [simplest_elim (constr_of_reference id);
     clear_global id;
     tclDO 2 intro;
     (wrap 1 false tacrec seq)]

let ll_arrow_tac a b c id tacrec seq=
  let cc=mkProd(Anonymous,a,(lift 1 b)) in
  let d=mkLambda (Anonymous,b,
		  mkApp ((constr_of_reference id),
			 [|mkLambda (Anonymous,(lift 1 a),(mkRel 2))|])) in
    tclTHENS (cut c)
      [tclTHENLIST
	 [intro;
	  clear_global id;
	  wrap 1 false tacrec seq];
       tclTHENS (cut cc) 
         [exact_no_check (constr_of_reference id); 
	  tclTHENLIST 
	    [generalize [d];
	     intro;
	     clear_global id;
	     tclSOLVE [wrap 1 true tacrec seq]]]]

let ll_atom_tac a id tacrec seq=
  try 
    tclTHENLIST
      [generalize [mkApp(constr_of_reference id,
			 [|constr_of_reference (find_left a seq)|])];
       clear_global id;
       intro;
       wrap 1 false tacrec seq] 
  with Not_found->tclFAIL 0 "No link" 

let ll_false_tac id tacrec seq=
  tclTHEN (clear_global id) (wrap 0 false tacrec seq)

let left_false_tac id=
  simplest_elim (constr_of_reference id)

(*We use this function for and, or, exists*)

let ll_ind_tac ind largs id tacrec seq gl= 
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
	    wrap lp false tacrec seq]
   with Dependent_Inductive | Invalid_argument _ ->tclFAIL 0 "") gl

let ll_forall_tac prod id tacrec seq=
  tclTHENS (cut prod)
    [tclTHENLIST
       [(fun gls->generalize 
	   [mkApp(constr_of_reference id,
		  [|mkVar (Tacmach.pf_nth_hyp_id gls 1)|])] gls);
	clear_global id;
	intro;
	tclSOLVE [wrap 1 false tacrec (deepen seq)]];
       tclSOLVE [wrap 0 true tacrec (deepen seq)]]

