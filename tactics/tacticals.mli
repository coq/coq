(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Sign
open Tacmach
open Proof_type
open Clenv
open Reduction
open Pattern
open Wcclausenv
(*i*)

(* Tacticals i.e. functions from tactics to tactics. *)

val tclIDTAC         : tactic
val tclORELSE        : tactic -> tactic -> tactic
val tclTHEN          : tactic -> tactic -> tactic
val tclTHENSEQ       : tactic list -> tactic
val tclTHENLIST      : tactic list -> tactic
val tclTHEN_i        : tactic -> (int -> tactic) -> tactic
val tclTHENFIRST     : tactic -> tactic -> tactic
val tclTHENLAST      : tactic -> tactic -> tactic
val tclTHENS         : tactic -> tactic list -> tactic
val tclTHENSV        : tactic -> tactic array -> tactic
val tclTHENSLASTn    : tactic -> tactic -> tactic array -> tactic
val tclTHENLASTn     : tactic -> tactic array -> tactic
val tclTHENSFIRSTn   : tactic -> tactic array -> tactic -> tactic
val tclTHENFIRSTn    : tactic -> tactic array -> tactic
val tclREPEAT        : tactic -> tactic
val tclREPEAT_MAIN   : tactic -> tactic
val tclFIRST         : tactic list -> tactic
val tclSOLVE         : tactic list -> tactic
val tclTRY           : tactic -> tactic
val tclINFO          : tactic -> tactic
val tclCOMPLETE      : tactic -> tactic
val tclAT_LEAST_ONCE : tactic -> tactic
val tclFAIL          : int -> tactic
val tclDO            : int -> tactic -> tactic
val tclPROGRESS      : tactic -> tactic
val tclWEAK_PROGRESS : tactic -> tactic
val tclNOTSAMEGOAL   : tactic -> tactic
val tclTHENTRY       : tactic -> tactic -> tactic

val tclNTH_HYP       : int -> (constr -> tactic) -> tactic
val tclMAP           : ('a -> tactic) -> 'a list -> tactic
val tclLAST_HYP      : (constr -> tactic) -> tactic
val tclTRY_sign      : (constr -> tactic) -> named_context -> tactic
val tclTRY_HYPS      : (constr -> tactic) -> tactic

val unTAC            : tactic -> goal sigma -> proof_tree sigma

(*s Clause tacticals. *)

type clause = identifier option

val nth_clause  : int -> goal sigma -> clause
val clause_type : clause -> goal sigma -> constr

val pf_matches : goal sigma -> constr_pattern -> constr -> (int * constr) list
val pf_is_matching : goal sigma -> constr_pattern -> constr -> bool

val allHyps    : goal sigma -> identifier list
val afterHyp   : identifier -> goal sigma -> named_context
val lastHyp    : goal sigma -> identifier
val nLastHyps  : int -> goal sigma -> named_context

val allClauses : goal sigma -> clause list

val onCL           : (goal sigma -> clause list) -> 
                     (clause list -> tactic) -> tactic
val tryAllClauses  : (clause -> tactic) -> tactic
val onAllClauses   : (clause -> tactic) -> tactic
val onClause       : (clause -> tactic) -> clause -> tactic
val onAllClausesLR : (clause -> tactic) -> tactic
val onNthLastHyp   : int -> (clause -> tactic) -> tactic
val clauseTacThen  : (clause -> tactic) -> tactic -> clause -> tactic
val if_tac         : (goal sigma -> bool) -> tactic -> (tactic) -> tactic
val ifOnClause     : 
  (clause * types -> bool) ->
    (clause -> tactic) -> (clause -> tactic) -> clause -> tactic
val ifOnHyp        : 
  (identifier * types -> bool) ->
    (identifier -> tactic) -> (identifier -> tactic) -> identifier -> tactic

val onHyps         : (goal sigma -> named_context) -> 
                     (named_context -> tactic) -> tactic
val tryAllHyps     : (identifier -> tactic) -> tactic
val onNLastHyps    : int -> (named_declaration -> tactic) -> tactic
val onLastHyp      : (identifier -> tactic) -> tactic

(*s Elimination tacticals. *)

type branch_args = { 
  ity        : inductive;   (* the type we were eliminating on *)
  largs      : constr list; (* its arguments *)
  branchnum  : int;         (* the branch number *)
  pred       : constr;      (* the predicate we used *)
  nassums    : int;         (* the number of assumptions to be introduced *)
  branchsign : bool list }  (* the signature of the branch.
                               true=recursive argument, false=constant *)

type branch_assumptions = {
  ba        : branch_args;     (* the branch args *)
  assums    : named_context;   (* the list of assumptions introduced *)
  cargs     : identifier list; (* the constructor arguments *)
  constargs : identifier list; (* the CONSTANT constructor arguments *)
  recargs   : identifier list; (* the RECURSIVE constructor arguments *)
  indargs   : identifier list} (* the inductive arguments *)

val elimination_sort_of_goal : goal sigma -> sorts_family
val elimination_sort_of_hyp  : identifier -> goal sigma -> sorts_family

val general_elim_then_using :
  constr ->  (inductive -> bool list array) -> 
    (branch_args -> tactic) -> constr option -> 
      (arg_bindings * arg_bindings) -> constr -> tactic
	  
val elimination_then_using :
  (branch_args -> tactic) -> constr option -> 
    (arg_bindings * arg_bindings) -> constr -> tactic

val elimination_then :
  (branch_args -> tactic) -> 
    (arg_bindings * arg_bindings) -> constr -> tactic

val case_then_using :
  (branch_args -> tactic) -> 
    constr option -> (arg_bindings * arg_bindings) -> constr -> tactic

val case_nodep_then_using :
  (branch_args -> tactic) -> 
    constr option -> (arg_bindings * arg_bindings) -> constr -> tactic

val simple_elimination_then :
  (branch_args -> tactic) -> constr -> tactic

val elim_on_ba : (branch_assumptions -> tactic) -> branch_args  -> tactic 
val case_on_ba : (branch_assumptions -> tactic) -> branch_args  -> tactic 
