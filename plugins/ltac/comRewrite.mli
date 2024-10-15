(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constrexpr

type rewrite_attributes
val rewrite_attributes : rewrite_attributes Attributes.attribute

val declare_relation
  : rewrite_attributes
  -> ?binders:local_binder_expr list
  -> constr_expr
  -> constr_expr
  -> Id.t
  -> constr_expr option
  -> constr_expr option
  -> constr_expr option
  -> unit

val add_setoid
  : rewrite_attributes
  -> local_binder_expr list
  -> constr_expr
  -> constr_expr
  -> constr_expr
  -> Id.t
  -> unit

val add_morphism_interactive : rewrite_attributes ->
  tactic:unit Proofview.tactic -> constr_expr -> Id.t -> Declare.Proof.t
val add_morphism_as_parameter : rewrite_attributes -> constr_expr -> Id.t -> unit

val add_morphism
  :  rewrite_attributes
  -> tactic:unit Proofview.tactic
  -> local_binder_expr list
  -> constr_expr
  -> constr_expr
  -> Id.t
  -> Declare.Proof.t
