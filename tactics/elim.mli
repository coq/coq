
(* $Id$ *)

(*i*)
open Names
open Term
open Proof_type
open Tacmach
open Tacticals
(*i*)

(* Eliminations tactics. *)

val introElimAssumsThen :
  (branch_assumptions -> tactic) -> branch_args -> tactic

val introCaseAssumsThen :
  (branch_assumptions -> tactic) -> branch_args -> tactic

val general_decompose_clause : (clause * constr -> bool) -> clause -> tactic
val general_decompose        : (clause * constr -> bool) -> constr -> tactic
val decompose_nonrec         : constr -> tactic
val decompose_and            : constr -> tactic
val decompose_or             : constr -> tactic
val h_decompose              : identifier list -> constr -> tactic

val double_ind : int -> int -> tactic

val intro_pattern     : intro_pattern      -> tactic
val intros_pattern    : intro_pattern list -> tactic
val dyn_intro_pattern : tactic_arg list    -> tactic
val v_intro_pattern   : tactic_arg list    -> tactic
val h_intro_pattern   : intro_pattern      -> tactic
