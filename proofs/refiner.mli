
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Term
open Sign
open Evd
open Proof_trees
open Proof_type
open Tacexpr
(*i*)

(* The refiner (handles primitive rules and high-level tactics). *)

val sig_it  : 'a sigma -> 'a
val sig_sig : 'a sigma -> evar_map

val project_with_focus : goal sigma -> named_context sigma

val unpackage : 'a sigma -> evar_map ref * 'a
val repackage : evar_map ref -> 'a -> 'a sigma
val apply_sig_tac :
  evar_map ref -> ('a sigma -> 'b sigma * 'c) -> 'a -> 'b * 'c

type transformation_tactic = proof_tree -> (goal list * validation)

val add_tactic             : string -> (closed_generic_argument list -> tactic) -> unit
val overwriting_add_tactic : string -> (closed_generic_argument list -> tactic) -> unit
val lookup_tactic          : string -> (closed_generic_argument list) -> tactic

(*s Hiding the implementation of tactics. *)

(* [abstract_tactic tac] hides the (partial) proof produced by [tac] under
   a single proof node *)
val abstract_tactic : atomic_tactic_expr -> tactic -> tactic
val abstract_tactic_expr : tactic_expr -> tactic -> tactic
val abstract_extended_tactic : string -> closed_generic_argument list -> tactic -> tactic

val refiner : rule -> tactic
val vernac_tactic : string * closed_generic_argument list -> tactic
val frontier : transformation_tactic
val list_pf : proof_tree -> goal list
val unTAC : tactic -> goal sigma -> proof_tree sigma

val local_Constraints : tactic

(* [frontier_map f n p] applies f on the n-th open subgoal of p and
   rebuilds proof-tree.
   n=1 for first goal, n negative counts from the right *)
val frontier_map :
  (proof_tree -> proof_tree) -> int -> proof_tree -> proof_tree

(* [frontier_mapi f p] applies (f i) on the i-th open subgoal of p. *)
val frontier_mapi :
  (int -> proof_tree -> proof_tree) -> proof_tree -> proof_tree

(*s Tacticals. *)

(* [tclIDTAC] is the identity tactic without message printing*)
val tclIDTAC          : tactic
val tclIDTAC_MESSAGE  : string -> tactic


(* [tclTHEN tac1 tac2 gls] applies the tactic [tac1] to [gls] and applies
   [tac2] to every resulting subgoals *)
val tclTHEN          : tactic -> tactic -> tactic

(* [tclTHENLIST [t1;..;tn]] applies [t1] THEN [t2] ... THEN [tn]. More
   convenient than [tclTHEN] when [n] is large *)
val tclTHENLIST      : tactic list -> tactic

(* [tclTHEN_i tac1 tac2 gls] applies the tactic [tac1] to [gls] and applies
   [(tac2 i)] to the [i]$^{th}$ resulting subgoal (starting from 1) *)
val tclTHEN_i        : tactic -> (int -> tactic) -> tactic

(* [tclTHENLAST tac1 tac2 gls] applies the tactic [tac1] to [gls] and [tac2]
   to the last resulting subgoal (previously called [tclTHENL]) *)
val tclTHENLAST         : tactic -> tactic -> tactic

(* [tclTHENFIRST tac1 tac2 gls] applies the tactic [tac1] to [gls] and [tac2]
   to the first resulting subgoal *)
val tclTHENFIRST         : tactic -> tactic -> tactic

(* [tclTHENS tac1 [|t1 ; ... ; tn|] gls] applies the tactic [tac1] to
   [gls] and applies [t1],..., [tn] to the [n] resulting subgoals. Raises
   an error if the number of resulting subgoals is not [n] *)
val tclTHENSV         : tactic -> tactic array -> tactic

(* Same with a list of tactics *)
val tclTHENS         : tactic -> tactic list -> tactic

(* [tclTHENST] is renamed [tclTHENSFIRSTn]
val tclTHENST        : tactic -> tactic array -> tactic -> tactic
*)

(* [tclTHENSLASTn tac1 [t1 ; ... ; tn] tac2 gls] applies [t1],...,[tn] on the
   last [n] resulting subgoals and [tac2] on the remaining first subgoals *)
val tclTHENSLASTn     : tactic -> tactic -> tactic array -> tactic

(* [tclTHENSFIRSTn tac1 [t1 ; ... ; tn] tac2 gls] first applies [tac1], then
   applies [t1],...,[tn] on the first [n] resulting subgoals and
   [tac2] for the remaining last subgoals (previously called tclTHENST) *)
val tclTHENSFIRSTn : tactic -> tactic array -> tactic -> tactic

(* [tclTHENLASTn tac1 [t1 ; ... ; tn] gls] first applies [tac1] then,
   applies [t1],...,[tn] on the last [n] resulting subgoals and leaves
   unchanged the other subgoals *)
val tclTHENLASTn    : tactic -> tactic array -> tactic

(* [tclTHENFIRSTn tac1 [t1 ; ... ; tn] gls] first applies [tac1] then,
   applies [t1],...,[tn] on the first [n] resulting subgoals and leaves
   unchanged the other subgoals (previously called [tclTHENSI]) *)
val tclTHENFIRSTn   : tactic -> tactic array -> tactic

(* A special exception for levels for the Fail tactic *)
exception FailError of int * string

val tclORELSE        : tactic -> tactic -> tactic
val tclREPEAT        : tactic -> tactic
val tclREPEAT_MAIN   : tactic -> tactic
val tclFIRST         : tactic list -> tactic
val tclSOLVE         : tactic list -> tactic
val tclTRY           : tactic -> tactic
val tclTHENTRY       : tactic -> tactic -> tactic
val tclCOMPLETE      : tactic -> tactic
val tclAT_LEAST_ONCE : tactic -> tactic
val tclFAIL          : int -> string -> tactic
val tclDO            : int -> tactic -> tactic
val tclPROGRESS      : tactic -> tactic
val tclWEAK_PROGRESS : tactic -> tactic
val tclNOTSAMEGOAL   : tactic -> tactic
val tclINFO          : tactic -> tactic

(* [tclIFTHENELSE tac1 tac2 tac3 gls] first applies [tac1] to [gls] then,
   if it succeeds, applies [tac2] to the resulting subgoals, 
   and if not applies [tac3] to the initial goal [gls] *)
val tclIFTHENELSE    : tactic -> tactic -> tactic -> tactic
val tclIFTHENSELSE   : tactic -> tactic list -> tactic ->tactic
val tclIFTHENSVELSE   : tactic -> tactic array -> tactic ->tactic

(*s Tactics handling a list of goals. *)

type validation_list = proof_tree list -> proof_tree list

type tactic_list = (goal list sigma) -> (goal list sigma) * validation_list

val tclFIRSTLIST       : tactic_list list -> tactic_list
val tclIDTAC_list      : tactic_list
val first_goal         : 'a list sigma -> 'a sigma
val apply_tac_list     : tactic -> tactic_list
val then_tactic_list   : tactic_list -> tactic_list -> tactic_list
val tactic_list_tactic : tactic_list -> tactic
val goal_goal_list     : 'a sigma -> 'a list sigma


(*s Functions for handling the state of the proof editor. *)

type pftreestate

val proof_of_pftreestate : pftreestate -> proof_tree
val cursor_of_pftreestate : pftreestate -> int list
val is_top_pftreestate : pftreestate -> bool
val evc_of_pftreestate : pftreestate -> evar_map
val top_goal_of_pftreestate : pftreestate -> goal sigma
val nth_goal_of_pftreestate : int -> pftreestate -> goal sigma

val traverse : int -> pftreestate -> pftreestate
val solve_nth_pftreestate : int -> tactic -> pftreestate -> pftreestate
val solve_pftreestate : tactic -> pftreestate -> pftreestate

(* a weak version of logical undoing, that is really correct only *)
(* if there are no existential variables.                         *)
val weak_undo_pftreestate : pftreestate -> pftreestate

val mk_pftreestate : goal -> pftreestate
val extract_open_pftreestate : pftreestate -> constr * Termops.metamap
val extract_pftreestate : pftreestate -> constr
val first_unproven : pftreestate -> pftreestate
val last_unproven : pftreestate -> pftreestate
val nth_unproven : int -> pftreestate -> pftreestate
val node_prev_unproven : int -> pftreestate -> pftreestate
val node_next_unproven : int -> pftreestate -> pftreestate
val next_unproven : pftreestate -> pftreestate
val prev_unproven : pftreestate -> pftreestate
val top_of_tree : pftreestate -> pftreestate
val change_constraints_pftreestate 
  : evar_map -> pftreestate -> pftreestate


(*s Pretty-printers. *)

(*i*)
open Pp
(*i*)

val print_proof : evar_map -> named_context -> proof_tree -> std_ppcmds
val pr_rule     : rule -> std_ppcmds
val pr_tactic   : tactic_expr -> std_ppcmds
val print_script :
  bool -> evar_map -> named_context -> proof_tree -> std_ppcmds
val print_treescript :
  bool -> evar_map -> named_context -> proof_tree -> std_ppcmds
