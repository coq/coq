(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Declarations

(** {6 Cooking the constants. } *)

type recipe = { from : constant_body; info : cooking_info }

type inline = bool

type 'opaque result = {
  cook_body : (constr, 'opaque) constant_def;
  cook_type : types;
  cook_universes : universes;
  cook_relevance : Sorts.relevance;
  cook_inline : inline;
  cook_context : Names.Id.Set.t option;
  cook_flags : typing_flags;
}

val cook_constant : recipe -> cooking_info Opaqueproof.opaque result
val cook_constr : cooking_info list ->
  (constr * unit Opaqueproof.delayed_universes) -> (constr * unit Opaqueproof.delayed_universes)

val cook_inductive :
  cooking_info -> mutual_inductive_body -> mutual_inductive_body

(** {6 Utility functions used in module [Discharge]. } *)

val expmod_constr : work_list -> constr -> constr
