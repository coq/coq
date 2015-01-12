(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Errors
open Util
open Names
open Term
open Vars
open Tacmach
open Tactics
open Tacticals
open Termops
open Formula
open Sequent
open Globnames
open Locus

type seqtac= (Sequent.t -> tactic) -> Sequent.t -> tactic

type lseqtac= global_reference -> seqtac

type 'a with_backtracking = tactic -> 'a

let wrap n b continue seq gls=
  Control.check_for_interrupt ();
  let nc=pf_hyps gls in
  let env=pf_env gls in
  let rec aux i nc ctx=
    if i<=0 then seq else
      match nc with
	  []->anomaly (Pp.str "Not the expected number of hyps")
	| ((id,_,typ) as nd)::q->
	    if occur_var env id (pf_concl gls) ||
	      List.exists (occur_var_in_decl env id) ctx then
		(aux (i-1) q (nd::ctx))
	    else
	      add_formula Hyp (VarRef id) typ (aux (i-1) q (nd::ctx)) gls in
  let seq1=aux n nc [] in
  let seq2=if b then
    add_formula Concl dummy_id (pf_concl gls) seq1 gls else seq1 in
    continue seq2 gls

let basename_of_global=function
    VarRef id->id
  | _->assert false

let clear_global=function
    VarRef id->clear [id]
  | _->tclIDTAC

(* connection rules *)

let axiom_tac t seq=
  try pf_constr_of_global (find_left t seq) exact_no_check
  with Not_found->tclFAIL 0 (Pp.str "No axiom link")

let ll_atom_tac a backtrack id continue seq=
  tclIFTHENELSE
    (try
      tclTHENLIST
	[pf_constr_of_global (find_left a seq) (fun left ->
	  pf_constr_of_global id (fun id -> 
	    generalize [mkApp(id, [|left|])]));
	 clear_global id;
	 Proofview.V82.of_tactic intro]
    with Not_found->tclFAIL 0 (Pp.str "No link"))
    (wrap 1 false continue seq) backtrack

(* right connectives rules *)

let and_tac backtrack continue seq=
  tclIFTHENELSE (Proofview.V82.of_tactic simplest_split) (wrap 0 true continue seq) backtrack

let or_tac backtrack continue seq=
  tclORELSE
    (Proofview.V82.of_tactic (any_constructor false (Some (Proofview.V82.tactic (tclCOMPLETE (wrap 0 true continue seq))))))
    backtrack

let arrow_tac backtrack continue seq=
  tclIFTHENELSE (Proofview.V82.of_tactic intro) (wrap 1 true continue seq)
    (tclORELSE
       (tclTHEN (Proofview.V82.of_tactic introf) (tclCOMPLETE (wrap 1 true continue seq)))
       backtrack)
(* left connectives rules *)

let left_and_tac ind backtrack id continue seq gls=
 let n=(construct_nhyps ind gls).(0) in
   tclIFTHENELSE
     (tclTHENLIST
      [Proofview.V82.of_tactic (Tacticals.New.pf_constr_of_global id simplest_elim);
       clear_global id;
       tclDO n (Proofview.V82.of_tactic intro)])
     (wrap n false continue seq)
     backtrack gls

let left_or_tac ind backtrack id continue seq gls=
  let v=construct_nhyps ind gls in
  let f n=
    tclTHENLIST
      [clear_global id;
       tclDO n (Proofview.V82.of_tactic intro);
       wrap n false continue seq] in
    tclIFTHENSVELSE
      (Proofview.V82.of_tactic (Tacticals.New.pf_constr_of_global id simplest_elim))
      (Array.map f v)
      backtrack gls

let left_false_tac id=
  Proofview.V82.of_tactic (Tacticals.New.pf_constr_of_global id simplest_elim)

(* left arrow connective rules *)

(* We use this function for false, and, or, exists *)

let ll_ind_tac (ind,u as indu) largs backtrack id continue seq gl=
     let rcs=ind_hyps 0 indu largs gl in
     let vargs=Array.of_list largs in
             (* construire le terme  H->B, le generaliser etc *)
     let myterm idc i=
       let rc=rcs.(i) in
       let p=List.length rc in
       let cstr=mkApp ((mkConstructU ((ind,(i+1)),u)),vargs) in
       let vars=Array.init p (fun j->mkRel (p-j)) in
       let capply=mkApp ((lift p cstr),vars) in
       let head=mkApp ((lift p idc),[|capply|]) in
         it_mkLambda_or_LetIn head rc in
       let lp=Array.length rcs in
       let newhyps idc =List.init lp (myterm idc) in
	 tclIFTHENELSE
	   (tclTHENLIST
	      [pf_constr_of_global id (fun idc -> generalize (newhyps idc));
	       clear_global id;
	       tclDO lp (Proofview.V82.of_tactic intro)])
	   (wrap lp false continue seq) backtrack gl

let ll_arrow_tac a b c backtrack id continue seq=
  let cc=mkProd(Anonymous,a,(lift 1 b)) in
  let d idc =mkLambda (Anonymous,b,
		  mkApp (idc, [|mkLambda (Anonymous,(lift 1 a),(mkRel 2))|])) in
    tclORELSE
      (tclTHENS (Proofview.V82.of_tactic (cut c))
	 [tclTHENLIST
	    [Proofview.V82.of_tactic introf;
	     clear_global id;
	     wrap 1 false continue seq];
	  tclTHENS (Proofview.V82.of_tactic (cut cc))
            [pf_constr_of_global id exact_no_check;
	     tclTHENLIST
	       [pf_constr_of_global id (fun idc -> generalize [d idc]);
		clear_global id;
		Proofview.V82.of_tactic introf;
		Proofview.V82.of_tactic introf;
		tclCOMPLETE (wrap 2 true continue seq)]]])
      backtrack

(* quantifier rules (easy side) *)

let forall_tac backtrack continue seq=
  tclORELSE
    (tclIFTHENELSE (Proofview.V82.of_tactic intro) (wrap 0 true continue seq)
       (tclORELSE
	  (tclTHEN (Proofview.V82.of_tactic introf) (tclCOMPLETE (wrap 0 true continue seq)))
	  backtrack))
    (if !qflag then
       tclFAIL 0 (Pp.str "reversible in 1st order mode")
     else
       backtrack)

let left_exists_tac ind backtrack id continue seq gls=
  let n=(construct_nhyps ind gls).(0) in
    tclIFTHENELSE
      (Proofview.V82.of_tactic (Tacticals.New.pf_constr_of_global id simplest_elim))
      (tclTHENLIST [clear_global id;
                    tclDO n (Proofview.V82.of_tactic intro);
                    (wrap (n-1) false continue seq)])
      backtrack
      gls

let ll_forall_tac prod backtrack id continue seq=
  tclORELSE
    (tclTHENS (Proofview.V82.of_tactic (cut prod))
       [tclTHENLIST
	  [Proofview.V82.of_tactic intro;
           pf_constr_of_global id (fun idc ->
	   (fun gls->
	      let id0=pf_nth_hyp_id gls 1 in
              let term=mkApp(idc,[|mkVar(id0)|]) in
		tclTHEN (generalize [term]) (clear [id0]) gls));
	   clear_global id;
	   Proofview.V82.of_tactic intro;
	   tclCOMPLETE (wrap 1 false continue (deepen seq))];
	tclCOMPLETE (wrap 0 true continue (deepen seq))])
    backtrack

(* rules for instantiation with unification moved to instances.ml *)

(* special for compatibility with old Intuition *)

let constant str = Coqlib.gen_constant "User" ["Init";"Logic"] str

let defined_connectives=lazy
  [AllOccurrences,EvalConstRef (fst (destConst (constant "not")));
   AllOccurrences,EvalConstRef (fst (destConst (constant "iff")))]

let normalize_evaluables=
  onAllHypsAndConcl
    (function
	 None->unfold_in_concl (Lazy.force defined_connectives)
       | Some id ->
	   unfold_in_hyp (Lazy.force defined_connectives) (id,InHypTypeOnly))
