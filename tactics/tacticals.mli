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
(*i*)

(* arnaud: trucs factices *)
type 'a sigma = 'a Evd.sigma
type goal = Evd.evar_info
type proof_instr = Decl_expr.proof_instr
type tactic_expr =
  (Goal.open_constr,
   constr_pattern,
   evaluable_global_reference,
   inductive,
   (*ltac_constant,*) int list array list,
   identifier,
   glob_tactic_expr)
     Tacexpr.gen_atomic_tactic_expr
type compound_rule=  
  | Tactic of tactic_expr * bool
  | Proof_instr of bool*proof_instr
type rule =
  | Prim of Logic.simple_tactic
  | Nested of compound_rule * proof_tree 
  | Decl_proof of bool
  | Daimon

and proof_tree = { goal: goal; ref: (rule * proof_tree list) option;
		    open_subgoals: int}
type validation = (proof_tree list -> proof_tree)
type tactic = goal sigma -> goal list sigma * validation

val abstract_tactic: ?dflt:bool -> tactic_expr -> tactic -> tactic
val abstract_extended_tactic :
  ?dflt:bool -> string -> typed_generic_argument list -> tactic -> tactic
(* arnaud: /trucs factices *)

(* Tacticals i.e. functions from tactics to tactics. *)

val tclIDTAC         : tactic
val tclIDTAC_MESSAGE : std_ppcmds -> tactic
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

val tclIFTHENELSE    : tactic -> tactic -> tactic -> tactic
val tclIFTHENSELSE   : tactic -> tactic list -> tactic -> tactic
val tclIFTHENSVELSE  : tactic -> tactic array -> tactic -> tactic

val tclIFTHENTRYELSEMUST : tactic -> tactic -> tactic

val unTAC            : tactic -> goal sigma -> proof_tree sigma

(*s Clause tacticals. *)

type simple_clause = identifier gsimple_clause
type clause = identifier gclause

val allClauses : 'a gclause
val allHyps : clause
val onHyp : identifier -> clause
val onConcl : 'a gclause

val nth_clause  : int -> goal sigma -> clause
val clause_type : clause -> goal sigma -> constr
val simple_clause_list_of : clause -> goal sigma -> simple_clause list

val pf_matches : goal sigma -> constr_pattern -> constr -> patvar_map
val pf_is_matching : goal sigma -> constr_pattern -> constr -> bool

val afterHyp   : identifier -> goal sigma -> named_context
val lastHyp    : goal sigma -> identifier
val nLastHyps  : int -> goal sigma -> named_context

val onCL           : (goal sigma -> clause) -> 
                     (clause -> tactic) -> tactic
val tryAllClauses  : (simple_clause -> tactic) -> tactic
val onAllClauses   : (simple_clause -> tactic) -> tactic
val onClause       : (clause -> tactic) -> clause -> tactic
val onClauses      : (simple_clause -> tactic) -> clause -> tactic
val onAllClausesLR : (simple_clause -> tactic) -> tactic
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
    (branch_args -> tactic) -> constr option -> 
      (arg_bindings * arg_bindings) -> constr -> tactic
	  
val elimination_then_using :
  (branch_args -> tactic) -> constr option -> 
    (arg_bindings * arg_bindings) -> constr -> Goal.proof_step Goal.sensitive

val elimination_then :
  (branch_args -> tactic) -> 
    (arg_bindings * arg_bindings) -> constr -> Goal.proof_step Goal.sensitive

val case_then_using :
  intro_pattern_expr -> (branch_args -> tactic) -> 
    constr option -> (arg_bindings * arg_bindings) -> constr -> Goal.proof_step Goal.sensitive

val case_nodep_then_using :
  intro_pattern_expr -> (branch_args -> tactic) -> 
    constr option -> (arg_bindings * arg_bindings) -> constr -> Goal.proof_step Goal.sensitive

val simple_elimination_then :
  (branch_args -> tactic) -> constr -> Goal.proof_step Goal.sensitive

val elim_on_ba : (branch_assumptions -> tactic) -> branch_args  -> tactic 
val case_on_ba : (branch_assumptions -> tactic) -> branch_args  -> tactic 
