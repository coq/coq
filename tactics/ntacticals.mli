(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Pp
open Names
open Term
open Sign
open Clenv
open Reduction
open Pattern
open Genarg
open Tacexpr
open Proofview
(*i*)

(* Tacticals i.e. functions from tactics to tactics. *)

val tclIDTAC         : unit tactic
val tclIDTAC_MESSAGE : std_ppcmds -> 'a tactic
val tclORELSE        : 'a tactic -> 'a tactic -> 'a tactic
val tclTHEN          : 'a tactic -> 'a tactic -> 'a tactic
val tclTHENSEQ       : unit tactic list -> unit tactic
val tclTHENLIST      : 'a tactic list -> 'a tactic
val tclTHEN_i        : 'a tactic -> (int -> 'a tactic) -> 'a tactic
val tclTHENFIRST     : 'a tactic -> 'a tactic -> 'a tactic
val tclTHENLAST      : 'a tactic -> 'a tactic -> 'a tactic
val tclTHENS         : 'a tactic -> 'a tactic list -> 'a tactic
val tclTHENSV        : 'a tactic -> 'a tactic array -> 'a tactic
val tclTHENSLASTn    : unit tactic -> unit tactic -> unit tactic array -> unit tactic
val tclTHENLASTn     : unit tactic -> unit tactic array -> unit tactic
val tclTHENSFIRSTn   : 'a tactic -> 'a tactic array -> 'a tactic -> 'a tactic
val tclTHENFIRSTn    : 'a tactic -> 'a tactic array -> 'a tactic
val tclREPEAT        : 'a tactic -> 'a tactic
val tclREPEAT_MAIN   : 'a tactic -> 'a tactic
val tclFIRST         : 'a tactic list -> 'a tactic
val tclSOLVE         : 'a tactic list -> 'a tactic
val tclTRY           : 'a tactic -> 'a tactic
val tclINFO          : 'a tactic -> 'a tactic
val tclCOMPLETE      : 'a tactic -> 'a tactic
val tclAT_LEAST_ONCE : 'a tactic -> 'a tactic
val tclFAIL          : int -> std_ppcmds -> 'a tactic
val tclDO            : int -> 'a tactic -> 'a tactic
val tclPROGRESS      : 'a tactic -> 'a tactic
val tclWEAK_PROGRESS : 'a tactic -> 'a tactic
val tclNOTSAMEGOAL   : 'a tactic -> 'a tactic
val tclTHENTRY       : 'a tactic -> 'a tactic -> 'a tactic

val tclNTH_HYP       : int Goal.sensitive -> 
                      (constr Goal.sensitive -> 'a tactic) -> 
                       'a tactic
val tclMAP           : ('a -> 'a tactic) -> 'a list -> 'a tactic
val tclLAST_HYP      : (constr Goal.sensitive -> 'a tactic) -> 'a tactic
val tclTRY_sign      : (constr -> 'a tactic) -> 
                        named_context -> 
                        'a tactic
val tclTRY_HYPS      : (constr Goal.sensitive -> 'a tactic) -> 'a tactic

val tclIFTHENELSE    : 'a tactic -> 'a tactic -> 'a tactic -> 'a tactic
val tclIFTHENSELSE   : 'a tactic -> 'a tactic list -> 'a tactic -> 'a tactic
val tclIFTHENSVELSE  : 'a tactic -> 'a tactic array -> 'a tactic -> 'a tactic

val tclIFTHENTRYELSEMUST : 'a tactic -> 'a tactic -> 'a tactic

(* arnaud: probablement mort
val unTAC            : 'a tactic -> goal sigma -> proof_tree sigma
*)

(*s Clause tacticals. *)

type simple_clause = identifier gsimple_clause
type clause = identifier gclause

val allClauses : 'a gclause
val allHyps : clause
val onHyp : identifier -> clause
val onConcl : 'a gclause

(* arnaud: débranchement temporaire

val nth_clause  : int Goal.sensitive -> clause Goal.sensitive
val clause_type : clause Goal.sensitive -> constr Goal.sensitive
val simple_clause_list_of : clause Goal.sensitive -> simple_clause list Goal.sensitive

val pf_matches : constr_pattern Goal.sensitive -> constr Goal.sensitive -> patvar_map Goal.sensitive
val pf_is_matching : constr_pattern Goal.sensitive -> constr Goal.sensitive -> bool Goal.sensitive
*)

val afterHyp   : identifier -> named_context Goal.sensitive

(*
val lastHyp    : identifier Goal.sensitive
val nLastHyps  : int Goal.sensitive -> named_context Goal.sensitive

val onCL           : clause Goal.sensitive -> 
                     (clause -> 'a tactic) -> 'a tactic
val tryAllClauses  : (simple_clause -> 'a tactic) -> 'a tactic
val onAllClauses   : (simple_clause -> 'a tactic) -> 'a tactic
val onClause       : (clause -> 'a tactic) -> clause -> 'a tactic
val onClauses      : (simple_clause -> 'a tactic) -> clause -> 'a tactic
val onAllClausesLR : (simple_clause -> 'a tactic) -> 'a tactic
val onNthLastHyp   : int -> (clause -> 'a tactic) -> 'a tactic
val clauseTacThen  : (clause -> 'a tactic) -> 'a tactic -> clause -> 'a tactic
val if_tac         : bool Goal.sensitive -> 'a tactic -> 'a tactic -> 'a tactic
val ifOnClause     : 
  (clause * types -> bool) ->
    (clause -> 'a tactic) -> (clause -> 'a tactic) -> clause -> 'a tactic
val ifOnHyp        : 
  (identifier * types -> bool) ->
    (identifier -> 'a tactic) -> (identifier -> 'a tactic) -> identifier -> 'a tactic

val onHyps         : named_context Goal.sensitive -> 
                     (named_context -> 'a tactic) -> 'a tactic
val tryAllHyps     : (identifier -> 'a tactic) -> 'a tactic
val onNLastHyps    : int -> (named_declaration -> 'a tactic) -> 'a tactic
val onLastHyp      : (identifier -> 'a tactic) -> 'a tactic
*)

(*s Elimination tacticals. *)

type branch_args = { 
  ity        : inductive;   (* the type we were eliminating on *)
  largs      : constr list; (* its arguments *)
  branchnum  : int;         (* the branch number *)
  pred       : constr;      (* the predicate we used *)
  nassums    : int;         (* the number of assumptions to be introduced *)
  branchsign : bool list;   (* the signature of the branch.
                               true=recursive argument, false=constant *)
  branchnames : intro_pattern_expr list}

type branch_assumptions = {
  ba        : branch_args;     (* the branch args *)
  assums    : named_context}   (* the list of assumptions introduced *)

(* Useful for [as intro_pattern] modifier *)
val compute_induction_names : 
  int -> intro_pattern_expr -> intro_pattern_expr list array

val elimination_sort_of_goal : sorts_family Goal.sensitive
val elimination_sort_of_hyp  : identifier -> sorts_family Goal.sensitive

val general_elim_then_using :
  constr -> (* isrec: *) bool -> intro_pattern_expr ->
    (branch_args -> 'a tactic) -> constr option -> 
      (arg_bindings * arg_bindings) -> constr -> 'a tactic
	  
val elimination_then_using :
  (branch_args -> 'a tactic) -> constr option -> 
    (arg_bindings * arg_bindings) -> constr -> Goal.proof_step Goal.sensitive

val elimination_then :
  (branch_args -> 'a tactic) -> 
    (arg_bindings * arg_bindings) -> constr -> Goal.proof_step Goal.sensitive

val case_then_using :
  intro_pattern_expr -> (branch_args -> 'a tactic) -> 
    constr option -> (arg_bindings * arg_bindings) -> constr -> Goal.proof_step Goal.sensitive

val case_nodep_then_using :
  intro_pattern_expr -> (branch_args -> 'a tactic) -> 
    constr option -> (arg_bindings * arg_bindings) -> constr -> Goal.proof_step Goal.sensitive

val simple_elimination_then :
  (branch_args -> 'a tactic) -> constr -> Goal.proof_step Goal.sensitive

val elim_on_ba : (branch_assumptions -> 'a tactic) -> branch_args  -> 'a tactic 
val case_on_ba : (branch_assumptions -> 'a tactic) -> branch_args  -> 'a tactic 
