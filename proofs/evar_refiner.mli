
(* $Id$ *)

(*i*)
open Names
open Term
open Sign
open Environ
open Evd
open Proof_trees
open Refiner
(*i*)

(* Refinement of existential variables. *)

val rc_of_pfsigma : proof_tree sigma -> readable_constraints
val rc_of_glsigma : goal sigma -> readable_constraints

type walking_constraints

type 'a result_w_tactic = walking_constraints -> walking_constraints * 'a
type w_tactic           = walking_constraints -> walking_constraints

val local_Constraints : 
  local_constraints -> goal sigma -> goal list sigma * validation

val startWalk : 
  goal sigma -> walking_constraints * (walking_constraints -> tactic)

val walking_THEN    : 'a result_w_tactic -> ('a -> tactic) -> tactic
val walking         : w_tactic -> tactic
val w_Focusing_THEN : 
  evar -> 'a result_w_tactic -> ('a -> w_tactic) -> w_tactic

val w_Declare    : evar -> constr -> w_tactic
val w_Declare_At : evar -> evar -> constr -> w_tactic
val w_Define     : evar -> constr -> w_tactic

val w_Underlying : walking_constraints -> evar_declarations
val w_env        : walking_constraints -> env
val w_hyps       : walking_constraints -> var_context
val w_type_of    : walking_constraints -> constr -> constr
val w_add_sign   : (identifier * typed_type) -> walking_constraints 
                     -> walking_constraints

val w_IDTAC      : w_tactic
val w_ORELSE     : w_tactic -> w_tactic -> w_tactic
val ctxt_type_of : readable_constraints -> constr -> constr

val evars_of     : readable_constraints -> constr -> local_constraints
