
(* $Id$ *)

(*i*)
open Term
open Sign
open Proof_trees
(*i*)

type 'a sigma = { 
  it : 'a ; 
  sigma : global_constraints }

val sig_it  : 'a sigma -> 'a
val sig_sig : 'a sigma -> global_constraints

val project_with_focus : goal sigma -> readable_constraints

val unpackage : 'a sigma -> global_constraints ref * 'a
val repackage : global_constraints ref -> 'a -> 'a sigma
val apply_sig_tac :
  global_constraints ref -> ('a sigma -> 'b sigma * 'c) -> 'a -> 'b * 'c

type validation = (proof_tree list -> proof_tree)

type tactic = goal sigma -> (goal list sigma * validation)

type transformation_tactic = proof_tree -> (goal list * validation)

val add_tactic             : string -> (tactic_arg list -> tactic) -> unit
val overwriting_add_tactic : string -> (tactic_arg list -> tactic) -> unit
val lookup_tactic          : string -> (tactic_arg list) -> tactic

val hide_tactic : 
  string -> (tactic_arg list -> tactic) -> (tactic_arg list -> tactic)

val overwrite_hidden_tactic : 
  string -> (tactic_arg list -> tactic) -> (tactic_arg list -> tactic)

val refiner : rule -> tactic

val extract_open_proof : context -> proof_tree -> constr * (int * constr) list
