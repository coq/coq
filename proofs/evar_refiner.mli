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

val rc_of_pfsigma : proof_tree sigma -> named_context sigma
val rc_of_glsigma : goal sigma -> named_context sigma

(* a [walking_constraints] is a structure associated to a specific
   goal; it collects all evars of which the goal depends.
  It has the following structure:
  [(identifying stamp, time stamp, 
  { focus : set of evars among decls of which the goal depends;
    hyps  : context of the goal;
    decls : a superset of evars of which the goal may depend })]
*)
type 'a result_w_tactic = named_context sigma -> named_context sigma * 'a

(* A [w_tactic] is a tactic which modifies the a set of evars of which
a goal depend, either by instantiating one, or by declaring a new
dependent goal *)
type w_tactic           = named_context sigma -> named_context sigma

val local_Constraints : 
  goal sigma -> goal list sigma * validation

val startWalk : 
  goal sigma -> named_context sigma * (named_context sigma -> tactic)

val walking_THEN    : 'a result_w_tactic -> ('a -> tactic) -> tactic
val walking         : w_tactic -> tactic
val w_Focusing_THEN : 
  evar -> 'a result_w_tactic -> ('a -> w_tactic) -> w_tactic

val w_Declare    : evar -> types -> w_tactic
val w_Define     : evar -> constr -> w_tactic

val w_Underlying : named_context sigma -> evar_map
val w_env        : named_context sigma -> env
val w_hyps       : named_context sigma -> named_context
val w_whd        : named_context sigma -> constr -> constr
val w_type_of    : named_context sigma -> constr -> constr
val w_add_sign   : (identifier * types) -> named_context sigma 
                     -> named_context sigma

val w_IDTAC      : w_tactic
val w_ORELSE     : w_tactic -> w_tactic -> w_tactic
val ctxt_type_of : named_context sigma -> constr -> constr
val w_whd_betadeltaiota : named_context sigma -> constr -> constr
val w_hnf_constr        : named_context sigma -> constr -> constr
val w_conv_x            : named_context sigma -> constr -> constr -> bool
val w_const_value       : named_context sigma -> constant -> constr
val w_defined_const     : named_context sigma -> constant -> bool
val w_defined_evar      : named_context sigma -> existential_key -> bool

val instantiate_pf     : int -> constr -> pftreestate -> pftreestate
val instantiate_pf_com : int -> Coqast.t -> pftreestate -> pftreestate
