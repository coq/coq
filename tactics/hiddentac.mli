
(* $Id$ *)

(*i*)
open Names
open Term
open Proof_trees
open Tacmach
open Tacentries
(*i*)

val h_clear           : identifier list -> tactic
val h_move            : bool -> identifier -> identifier -> tactic
val h_contradiction   : tactic
val h_reflexivity     : tactic
val h_symmetry        : tactic
val h_assumption      : tactic
val h_absurd          : constr -> tactic
val h_exact           : constr -> tactic
val h_one_constructor : int -> tactic
val h_any_constructor : tactic
val h_transitivity    : constr -> tactic
val h_simplest_left   : tactic
val h_simplest_right  : tactic
val h_split           : constr -> tactic
val h_apply           : constr -> constr substitution -> tactic
val h_simplest_apply  : constr -> tactic 
val h_cut             : constr -> tactic 
val h_simplest_elim   : constr -> tactic
val h_elimType        : constr -> tactic
val h_simplest_case   : constr -> tactic
val h_caseType        : constr -> tactic
val h_inductionInt    : int -> tactic 
val h_inductionId     : identifier -> tactic 
val h_destructInt     : int -> tactic
val h_destructId      : identifier -> tactic

