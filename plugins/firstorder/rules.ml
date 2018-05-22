(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Names
open EConstr
open Vars
open Tacmach.New
open Tactics
open Tacticals.New
open Proofview.Notations
open Termops
open Formula
open Sequent
open Globnames
open Locus

module NamedDecl = Context.Named.Declaration

type tactic = unit Proofview.tactic

type seqtac= (Sequent.t -> tactic) -> Sequent.t -> tactic

type lseqtac= GlobRef.t -> seqtac

type 'a with_backtracking = tactic -> 'a

let wrap n b continue seq =
  Proofview.Goal.nf_enter begin fun gls ->
  Control.check_for_interrupt ();
  let nc = Proofview.Goal.hyps gls in
  let env=pf_env gls in
  let sigma = project gls in
  let rec aux i nc ctx=
    if i<=0 then seq else
      match nc with
	  []->anomaly (Pp.str "Not the expected number of hyps.")
	| nd::q->
            let id = NamedDecl.get_id nd in
	    if occur_var env sigma id (pf_concl gls) ||
	      List.exists (occur_var_in_decl env sigma id) ctx then
		(aux (i-1) q (nd::ctx))
	    else
	      add_formula env sigma Hyp (VarRef id) (NamedDecl.get_type nd) (aux (i-1) q (nd::ctx)) in
  let seq1=aux n nc [] in
  let seq2=if b then
    add_formula env sigma Concl dummy_id (pf_concl gls) seq1 else seq1 in
    continue seq2
  end

let basename_of_global=function
    VarRef id->id
  | _->assert false

let clear_global=function
    VarRef id-> clear [id]
  | _->tclIDTAC

(* connection rules *)

let axiom_tac t seq =
  Proofview.Goal.enter begin fun gl ->
  try
    pf_constr_of_global (find_left (project gl) t seq) >>= fun c ->
    exact_no_check c
  with Not_found -> tclFAIL 0 (Pp.str "No axiom link")
  end

let ll_atom_tac a backtrack id continue seq =
  let open EConstr in
  tclIFTHENELSE
      (tclTHENLIST
	[(Proofview.tclEVARMAP >>= fun sigma ->
          let gr =
            try Proofview.tclUNIT (find_left sigma a seq)
            with Not_found -> tclFAIL 0 (Pp.str "No link")
          in
          gr >>= fun gr ->
          pf_constr_of_global gr >>= fun left ->
	  pf_constr_of_global id >>= fun id -> 
	    generalize [(mkApp(id, [|left|]))]);
	 clear_global id;
	 intro])
    (wrap 1 false continue seq) backtrack

(* right connectives rules *)

let and_tac backtrack continue seq=
  tclIFTHENELSE simplest_split (wrap 0 true continue seq) backtrack

let or_tac backtrack continue seq=
  tclORELSE
    (any_constructor false (Some (tclCOMPLETE (wrap 0 true continue seq))))
    backtrack

let arrow_tac backtrack continue seq=
  tclIFTHENELSE intro (wrap 1 true continue seq)
    (tclORELSE
       (tclTHEN introf (tclCOMPLETE (wrap 1 true continue seq)))
       backtrack)
(* left connectives rules *)

let left_and_tac ind backtrack id continue seq =
  Proofview.Goal.enter begin fun gl ->
  let n=(construct_nhyps (pf_env gl) ind).(0) in
   tclIFTHENELSE
     (tclTHENLIST
      [(pf_constr_of_global id >>= simplest_elim);
       clear_global id;
       tclDO n intro])
     (wrap n false continue seq)
     backtrack
  end

let left_or_tac ind backtrack id continue seq =
  Proofview.Goal.enter begin fun gl ->
  let v=construct_nhyps (pf_env gl) ind in
  let f n=
    tclTHENLIST
      [clear_global id;
       tclDO n intro;
       wrap n false continue seq] in
    tclIFTHENSVELSE
      (pf_constr_of_global id >>= simplest_elim)
      (Array.map f v)
      backtrack
  end

let left_false_tac id=
  Tacticals.New.pf_constr_of_global id >>= simplest_elim

(* left arrow connective rules *)

(* We use this function for false, and, or, exists *)

let ll_ind_tac (ind,u as indu) largs backtrack id continue seq =
  Proofview.Goal.enter begin fun gl ->
     let rcs=ind_hyps (pf_env gl) (project gl) 0 indu largs in
     let vargs=Array.of_list largs in
             (* construire le terme  H->B, le generaliser etc *)
     let myterm idc i=
       let rc=rcs.(i) in
       let p=List.length rc in
       let u = EInstance.make u in
       let cstr=mkApp ((mkConstructU ((ind,(i+1)),u)),vargs) in
       let vars=Array.init p (fun j->mkRel (p-j)) in
       let capply=mkApp ((lift p cstr),vars) in
       let head=mkApp ((lift p idc),[|capply|]) in
         EConstr.it_mkLambda_or_LetIn head rc in
       let lp=Array.length rcs in
       let newhyps idc =List.init lp (myterm idc) in
	 tclIFTHENELSE
	   (tclTHENLIST
	      [(pf_constr_of_global id >>= fun idc -> generalize (newhyps idc));
	       clear_global id;
	       tclDO lp intro])
	   (wrap lp false continue seq) backtrack
  end

let ll_arrow_tac a b c backtrack id continue seq=
  let open EConstr in
  let open Vars in
  let cc=mkProd(Anonymous,a,(lift 1 b)) in
  let d idc = mkLambda (Anonymous,b,
		  mkApp (idc, [|mkLambda (Anonymous,(lift 1 a),(mkRel 2))|])) in
    tclORELSE
      (tclTHENS (cut c)
	 [tclTHENLIST
	    [introf;
	     clear_global id;
	     wrap 1 false continue seq];
	  tclTHENS (cut cc)
            [(pf_constr_of_global id >>= fun c -> exact_no_check c);
	     tclTHENLIST
	       [(pf_constr_of_global id >>= fun idc -> generalize [d idc]);
		clear_global id;
		introf;
		introf;
		tclCOMPLETE (wrap 2 true continue seq)]]])
      backtrack

(* quantifier rules (easy side) *)

let forall_tac backtrack continue seq=
  tclORELSE
    (tclIFTHENELSE intro (wrap 0 true continue seq)
       (tclORELSE
	  (tclTHEN introf (tclCOMPLETE (wrap 0 true continue seq)))
	  backtrack))
    (if !qflag then
       tclFAIL 0 (Pp.str "reversible in 1st order mode")
     else
       backtrack)

let left_exists_tac ind backtrack id continue seq =
  Proofview.Goal.enter begin fun gl ->
  let n=(construct_nhyps (pf_env gl) ind).(0) in
    tclIFTHENELSE
      (Tacticals.New.pf_constr_of_global id >>= simplest_elim)
      (tclTHENLIST [clear_global id;
                    tclDO n intro;
                    (wrap (n-1) false continue seq)])
      backtrack
  end

let ll_forall_tac prod backtrack id continue seq=
  tclORELSE
    (tclTHENS (cut prod)
       [tclTHENLIST
	  [intro;
           (pf_constr_of_global id >>= fun idc ->
	   Proofview.Goal.enter begin fun gls->
              let open EConstr in
	      let id0 = List.nth (pf_ids_of_hyps gls) 0 in
              let term=mkApp(idc,[|mkVar(id0)|]) in
              tclTHEN (generalize [term]) (clear [id0])
           end);
	   clear_global id;
	   intro;
	   tclCOMPLETE (wrap 1 false continue (deepen seq))];
	tclCOMPLETE (wrap 0 true continue (deepen seq))])
    backtrack

(* rules for instantiation with unification moved to instances.ml *)

(* special for compatibility with old Intuition *)

let constant str = UnivGen.constr_of_global
  @@ Coqlib.coq_reference "User" ["Init";"Logic"] str

let defined_connectives=lazy
  [AllOccurrences,EvalConstRef (fst (Constr.destConst (constant "not")));
   AllOccurrences,EvalConstRef (fst (Constr.destConst (constant "iff")))]

let normalize_evaluables=
  Proofview.Goal.enter begin fun gl ->
    unfold_in_concl (Lazy.force defined_connectives) <*>
    tclMAP
      (fun id -> unfold_in_hyp (Lazy.force defined_connectives) (id,InHypTypeOnly))
      (pf_ids_of_hyps gl)
  end
