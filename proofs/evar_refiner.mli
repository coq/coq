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
open Environ
open Evd
open Proof_trees
open Proof_type
open Refiner
(*i*)

(* Refinement of existential variables. *)

val rc_of_pfsigma : proof_tree sigma -> readable_constraints
val rc_of_glsigma : goal sigma -> readable_constraints

(* a [walking_constraints] is a structure associated to a specific
   goal; it collects all evars of which the goal depends.
  It has the following structure:
  [(identifying stamp, time stamp, 
  { focus : set of evars among decls of which the goal depends;
    hyps  : context of the goal;
    decls : a superset of evars of which the goal may depend })]
*)
type walking_constraints

type 'a result_w_tactic = walking_constraints -> walking_constraints * 'a

(* A [w_tactic] is a tactic which modifies the a set of evars of which
a goal depend, either by instantiating one, or by declaring a new
dependent goal *)
type w_tactic           = walking_constraints -> walking_constraints

val local_Constraints : 
  local_constraints -> goal sigma -> goal list sigma * validation

val startWalk : 
  goal sigma -> walking_constraints * (walking_constraints -> tactic)

val walking_THEN    : 'a result_w_tactic -> ('a -> tactic) -> tactic
val walking         : w_tactic -> tactic
val w_Focusing_THEN : 
  evar -> 'a result_w_tactic -> ('a -> w_tactic) -> w_tactic

val w_Declare    : evar -> constr * constr -> w_tactic
val w_Declare_At : evar -> evar -> constr * constr -> w_tactic
val w_Define     : evar -> constr -> w_tactic

val w_Underlying : walking_constraints -> enamed_declarations
val w_env        : walking_constraints -> env
val w_hyps       : walking_constraints -> named_context
val w_whd        : walking_constraints -> constr -> constr
val w_type_of    : walking_constraints -> constr -> constr
val w_add_sign   : (identifier * types) -> walking_constraints 
                     -> walking_constraints

val w_IDTAC      : w_tactic
val w_ORELSE     : w_tactic -> w_tactic -> w_tactic
val ctxt_type_of : readable_constraints -> constr -> constr
val w_whd_betadeltaiota : walking_constraints -> constr -> constr
val w_hnf_constr        : walking_constraints -> constr -> constr
val w_conv_x            : walking_constraints -> constr -> constr -> bool
val w_const_value       : walking_constraints -> constant -> constr
val w_defined_const     : walking_constraints -> constant -> bool
val w_defined_evar      : walking_constraints -> existential_key -> bool

val evars_of     : readable_constraints -> constr -> local_constraints

val instantiate_pf     : int -> constr -> pftreestate -> pftreestate
val instantiate_pf_com : int -> Coqast.t -> pftreestate -> pftreestate
