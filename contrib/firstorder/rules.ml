(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util
open Names
open Term
open Tacmach
open Tactics
open Tacticals
open Termops
open Declarations
open Formula
open Sequent
open Libnames

type seqtac= (Sequent.t -> tactic) -> Sequent.t -> tactic

type lseqtac= global_reference -> seqtac

type 'a with_backtracking = tactic -> 'a

let wrap n b continue seq gls=
  check_for_interrupt ();
  let nc=pf_hyps gls in
  let env=pf_env gls in
  let rec aux i nc ctx=
    if i<=0 then seq else 
      match nc with
	  []->anomaly "Not the expected number of hyps"
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

let id_of_global=function
    VarRef id->id
  | _->assert false

let clear_global=function
    VarRef id->clear [id]
  | _->tclIDTAC
      

(* connection rules *)

let axiom_tac t seq=
  try exact_no_check (constr_of_global (find_left t seq)) 
  with Not_found->tclFAIL 0 (Pp.str "No axiom link")

let ll_atom_tac a backtrack id continue seq= 
  tclIFTHENELSE
    (try 
      tclTHENLIST
	[generalize [mkApp(constr_of_global id,
			   [|constr_of_global (find_left a seq)|])];
	 clear_global id;
	 intro]
    with Not_found->tclFAIL 0 (Pp.str "No link"))
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

let left_and_tac ind backtrack id continue seq gls=
 let n=(construct_nhyps ind gls).(0) in  
   tclIFTHENELSE
     (tclTHENLIST 
      [simplest_elim (constr_of_global id);
       clear_global id; 
       tclDO n intro])
     (wrap n false continue seq)
     backtrack gls

let left_or_tac ind backtrack id continue seq gls=
  let v=construct_nhyps ind gls in  
  let f n=
    tclTHENLIST
      [clear_global id;
       tclDO n intro;
       wrap n false continue seq] in
    tclIFTHENSVELSE
      (simplest_elim (constr_of_global id))
      (Array.map f v)
      backtrack gls

let left_false_tac id=
  simplest_elim (constr_of_global id)

(* left arrow connective rules *)

(* We use this function for false, and, or, exists *)

let ll_ind_tac ind largs backtrack id continue seq gl= 
     let rcs=ind_hyps 0 ind largs gl in
     let vargs=Array.of_list largs in
	     (* construire le terme  H->B, le generaliser etc *)   
     let myterm i=
       let rc=rcs.(i) in
       let p=List.length rc in
       let cstr=mkApp ((mkConstruct (ind,(i+1))),vargs) in
       let vars=Array.init p (fun j->mkRel (p-j)) in
       let capply=mkApp ((lift p cstr),vars) in
       let head=mkApp ((lift p (constr_of_global id)),[|capply|]) in
	 it_mkLambda_or_LetIn head rc in
       let lp=Array.length rcs in
       let newhyps=list_tabulate myterm lp in
	 tclIFTHENELSE
	   (tclTHENLIST 
	      [generalize newhyps;
	       clear_global id;
	       tclDO lp intro])
	   (wrap lp false continue seq) backtrack gl

let ll_arrow_tac a b c backtrack id continue seq=
  let cc=mkProd(Anonymous,a,(lift 1 b)) in
  let d=mkLambda (Anonymous,b,
		  mkApp ((constr_of_global id),
			 [|mkLambda (Anonymous,(lift 1 a),(mkRel 2))|])) in
    tclORELSE
      (tclTHENS (cut c)
	 [tclTHENLIST
	    [introf;
	     clear_global id;
	     wrap 1 false continue seq];
	  tclTHENS (cut cc) 
            [exact_no_check (constr_of_global id); 
	     tclTHENLIST 
	       [generalize [d];
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

let left_exists_tac ind backtrack id continue seq gls=
  let n=(construct_nhyps ind gls).(0) in  
    tclIFTHENELSE
      (simplest_elim (constr_of_global id))
      (tclTHENLIST [clear_global id;
                    tclDO n intro;
                    (wrap (n-1) false continue seq)]) 
      backtrack 
      gls
	
let ll_forall_tac prod backtrack id continue seq=
  tclORELSE
    (tclTHENS (cut prod)
       [tclTHENLIST
	  [intro;
	   (fun gls->
	      let id0=pf_nth_hyp_id gls 1 in
	      let term=mkApp((constr_of_global id),[|mkVar(id0)|]) in
		tclTHEN (generalize [term]) (clear [id0]) gls);  
	   clear_global id;
	   intro;
	   tclCOMPLETE (wrap 1 false continue (deepen seq))];
	tclCOMPLETE (wrap 0 true continue (deepen seq))])
    backtrack

(* rules for instantiation with unification moved to instances.ml *)

(* special for compatibility with old Intuition *)

let constant str = Coqlib.gen_constant "User" ["Init";"Logic"] str

let defined_connectives=lazy
  [all_occurrences,EvalConstRef (destConst (constant "not"));
   all_occurrences,EvalConstRef (destConst (constant "iff"))]

let normalize_evaluables=
  onAllClauses
    (function 
	 None->unfold_in_concl (Lazy.force defined_connectives)
       | Some ((_,id),_)-> 
	   unfold_in_hyp (Lazy.force defined_connectives) 
	   ((Rawterm.all_occurrences_expr,id),InHypTypeOnly))
