
(* $Id$ *)

(*i*)
open Names
open Term
open Sign
open Tacmach
open Proof_trees
open Clenv
open Reduction
open Pattern
open Wcclausenv
(*i*)

val tclIDTAC         : tactic
val tclORELSE        : tactic -> tactic -> tactic
val tclTHEN          : tactic -> tactic -> tactic
val tclTHEN_i        : tactic -> (int -> tactic) -> int -> tactic
val tclTHENL         : tactic -> tactic -> tactic
val tclTHENS         : tactic -> tactic list -> tactic
val tclREPEAT        : tactic -> tactic
val tclFIRST         : tactic list -> tactic
val tclTRY           : tactic -> tactic
val tclINFO          : tactic -> tactic
val tclCOMPLETE      : tactic -> tactic
val tclAT_LEAST_ONCE : tactic -> tactic
val tclFAIL          : tactic
val tclDO            : int -> tactic -> tactic
val tclPROGRESS      : tactic -> tactic
val tclWEAK_PROGRESS : tactic -> tactic
val tclNTH_HYP       : int -> (constr -> tactic) -> tactic
val tclMAP           : ('a -> tactic) -> 'a list -> tactic
val tclLAST_HYP      : (constr -> tactic) -> tactic
val tclTRY_sign      : (constr -> tactic) -> constr signature -> tactic
val tclTRY_HYPS      : (constr -> tactic) -> tactic

val dyn_tclIDTAC     : tactic_arg list -> tactic
val dyn_tclFAIL      : tactic_arg list -> tactic

(* Clause tacticals *)

type clause = identifier option

val tclTHEN_i1     : tactic -> (int -> tactic) -> tactic
val nth_clause  : int -> goal sigma -> clause
val clause_type : clause -> goal sigma -> constr

val matches      : goal sigma -> constr -> marked_term -> bool
val dest_match   : goal sigma -> constr -> marked_term -> constr list

val allHyps    : goal sigma -> clause list
val afterHyp   : identifier -> goal sigma -> clause list
val lastHyp    : goal sigma -> clause  list
val nLastHyps  : int -> goal sigma -> clause list
val allClauses : goal sigma -> clause list

val onCL           : (goal sigma -> clause list) -> 
                     (clause list -> tactic) -> tactic
val tryAllHyps     : (clause -> tactic) -> tactic
val tryAllClauses  : (clause -> tactic) -> tactic
val onAllClauses   : (clause -> tactic) -> tactic
val onClause       : (clause -> tactic) -> clause -> tactic
val onAllClausesLR : (clause -> tactic) -> tactic
val onLastHyp      : (clause -> tactic) -> tactic
val onNthLastHyp   : int -> (clause -> tactic) -> tactic
val onNLastHyps    : int -> (clause -> tactic) -> tactic
val clauseTacThen  : (clause -> tactic) -> tactic -> clause -> tactic
val if_tac         : (goal sigma -> bool) -> tactic -> (tactic) -> tactic
val ifOnClause     : (clause * constr -> bool) -> 
                      (clause -> tactic) -> 
                      (clause -> tactic) -> 
                       clause -> tactic

(* Usage : [ConclPattern concl pat tacast]
   if the term concl matches the pattern pat, (in sense of 
   Pattern.somatches, then replace ?1 ?2 metavars in tacast by the
   right values to build a tactic *)
(***
val conclPattern : constr -> constr -> CoqAst.t -> tactic
***)

(* Elimination tacticals *)

type branch_args = { 
  ity        : constr;      (* the type we were eliminating on *)
  largs      : constr list; (* its arguments *)
  branchnum  : int;         (* the branch number *)
  pred       : constr;      (* the predicate we used *)
  nassums    : int;         (* the number of assumptions to be introduced *)
  branchsign : bool list }  (* the signature of the branch.
                               true=recursive argument, false=constant *)

type branch_assumptions = {
  ba        : branch_args;     (* the branch args *)
  assums    : identifier list; (* the list of assumptions introduced *)
  cargs     : identifier list; (* the constructor arguments *)
  constargs : identifier list; (* the CONSTANT constructor arguments *)
  recargs   : identifier list; (* the RECURSIVE constructor arguments *)
  indargs   : identifier list} (* the inductive arguments *)

val sort_of_goal      : goal sigma -> sorts
val suff              : goal sigma -> constr -> string
val lookup_eliminator : context -> section_path -> string -> constr

val general_elim_then_using :
  constr ->  (constr -> int -> bool list) -> 
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
