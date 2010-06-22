(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Names
open Term
open Sign
open Tacmach
open Proof_type
open Clenv
open Reduction
open Pattern
open Genarg
open Tacexpr
open Termops
open Rawterm

(** Tacticals i.e. functions from tactics to tactics. *)

val tclNORMEVAR      : tactic
val tclIDTAC         : tactic
val tclIDTAC_MESSAGE : std_ppcmds -> tactic
val tclORELSE0       : tactic -> tactic -> tactic
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
val tclFAIL          : int -> std_ppcmds -> tactic
val tclFAIL_lazy     : int -> std_ppcmds Lazy.t -> tactic
val tclDO            : int -> tactic -> tactic
val tclWEAK_PROGRESS : tactic -> tactic
val tclPROGRESS      : tactic -> tactic
val tclNOTSAMEGOAL   : tactic -> tactic
val tclTHENTRY       : tactic -> tactic -> tactic
val tclMAP           : ('a -> tactic) -> 'a list -> tactic

val tclIFTHENELSE        : tactic -> tactic -> tactic -> tactic
val tclIFTHENSELSE       : tactic -> tactic list -> tactic -> tactic
val tclIFTHENSVELSE      : tactic -> tactic array -> tactic -> tactic
val tclIFTHENTRYELSEMUST : tactic -> tactic -> tactic

val tclFIRST_PROGRESS_ON : ('a -> tactic) -> 'a list -> tactic

(** {6 Tacticals applying to hypotheses } *)

val onNthHypId       : int -> (identifier -> tactic) -> tactic
val onNthHyp         : int -> (constr -> tactic) -> tactic
val onNthDecl        : int -> (named_declaration -> tactic) -> tactic
val onLastHypId      : (identifier -> tactic) -> tactic
val onLastHyp        : (constr -> tactic) -> tactic
val onLastDecl       : (named_declaration -> tactic) -> tactic
val onNLastHypsId    : int -> (identifier list -> tactic) -> tactic
val onNLastHyps      : int -> (constr list -> tactic) -> tactic
val onNLastDecls     : int -> (named_context -> tactic) -> tactic

val lastHypId   : goal sigma -> identifier
val lastHyp     : goal sigma -> constr
val lastDecl    : goal sigma -> named_declaration
val nLastHypsId : int -> goal sigma -> identifier list
val nLastHyps   : int -> goal sigma -> constr list
val nLastDecls  : int -> goal sigma -> named_context

val afterHyp    : identifier -> goal sigma -> named_context

val ifOnHyp     : (identifier * types -> bool) ->
                  (identifier -> tactic) -> (identifier -> tactic) ->
		   identifier -> tactic

val onHyps      : (goal sigma -> named_context) ->
                  (named_context -> tactic) -> tactic

(** {6 Tacticals applying to goal components } *)

(** A [simple_clause] is a set of hypotheses, possibly extended with
   the conclusion (conclusion is represented by None) *)

type simple_clause = identifier option list

(** A [clause] denotes occurrences and hypotheses in a
   goal; in particular, it can abstractly refer to the set of
   hypotheses independently of the effective contents of the current goal *)

type clause = identifier gclause

val simple_clause_of : clause -> goal sigma -> simple_clause

val allHypsAndConcl : clause
val allHyps         : clause
val onHyp           : identifier -> clause
val onConcl         : clause

val tryAllHyps          : (identifier -> tactic) -> tactic
val tryAllHypsAndConcl  : (identifier option -> tactic) -> tactic

val onAllHyps           : (identifier -> tactic) -> tactic
val onAllHypsAndConcl   : (identifier option -> tactic) -> tactic
val onAllHypsAndConclLR : (identifier option -> tactic) -> tactic

val onClause   : (identifier option -> tactic) -> clause -> tactic
val onClauseLR : (identifier option -> tactic) -> clause -> tactic

(** {6 An intermediate form of occurrence clause with no mention of occurrences } *)

(** A [hyp_location] is an hypothesis together with a position, in
   body if any, in type or in both *)

type hyp_location = identifier * hyp_location_flag

(** A [goal_location] is either an hypothesis (together with a position, in
   body if any, in type or in both) or the goal *)

type goal_location = hyp_location option

(** {6 A concrete view of occurrence clauses } *)

(** [clause_atom] refers either to an hypothesis location (i.e. an
   hypothesis with occurrences and a position, in body if any, in type
   or in both) or to some occurrences of the conclusion *)

type clause_atom =
  | OnHyp of identifier * occurrences_expr * hyp_location_flag
  | OnConcl of occurrences_expr

(** A [concrete_clause] is an effective collection of
  occurrences in the hypotheses and the conclusion *)

type concrete_clause = clause_atom list

(** This interprets an [clause] in a given [goal] context *)
val concrete_clause_of : clause -> goal sigma -> concrete_clause

(** {6 Elimination tacticals. } *)

type branch_args = {
  ity        : inductive;   (** the type we were eliminating on *)
  largs      : constr list; (** its arguments *)
  branchnum  : int;         (** the branch number *)
  pred       : constr;      (** the predicate we used *)
  nassums    : int;         (** the number of assumptions to be introduced *)
  branchsign : bool list;   (** the signature of the branch.
                               true=recursive argument, false=constant *)
  branchnames : intro_pattern_expr located list}

type branch_assumptions = {
  ba        : branch_args;     (** the branch args *)
  assums    : named_context}   (** the list of assumptions introduced *)

(** [check_disjunctive_pattern_size loc pats n] returns an appropriate 
   error message if |pats| <> n *)
val check_or_and_pattern_size :
  Util.loc -> or_and_intro_pattern_expr -> int -> unit

(** Tolerate "[]" to mean a disjunctive pattern of any length *)
val fix_empty_or_and_pattern : int -> or_and_intro_pattern_expr ->
  or_and_intro_pattern_expr

(** Useful for [as intro_pattern] modifier *)
val compute_induction_names :
  int -> intro_pattern_expr located option ->
    intro_pattern_expr located list array

val elimination_sort_of_goal : goal sigma -> sorts_family
val elimination_sort_of_hyp  : identifier -> goal sigma -> sorts_family
val elimination_sort_of_clause : identifier option -> goal sigma -> sorts_family

val general_elim_then_using :
  (inductive -> goal sigma -> constr) -> rec_flag ->
  intro_pattern_expr located option -> (branch_args -> tactic) ->
    constr option -> (arg_bindings * arg_bindings) -> inductive -> clausenv ->
    tactic

val elimination_then_using :
  (branch_args -> tactic) -> constr option ->
    (arg_bindings * arg_bindings) -> constr -> tactic

val elimination_then :
  (branch_args -> tactic) ->
    (arg_bindings * arg_bindings) -> constr -> tactic

val case_then_using :
  intro_pattern_expr located option -> (branch_args -> tactic) ->
    constr option -> (arg_bindings * arg_bindings) ->
      inductive -> clausenv -> tactic

val case_nodep_then_using :
  intro_pattern_expr located option -> (branch_args -> tactic) ->
    constr option -> (arg_bindings * arg_bindings) ->
      inductive -> clausenv -> tactic

val simple_elimination_then :
  (branch_args -> tactic) -> constr -> tactic

val elim_on_ba : (branch_assumptions -> tactic) -> branch_args  -> tactic
val case_on_ba : (branch_assumptions -> tactic) -> branch_args  -> tactic
