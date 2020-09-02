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

type recipe = { from : Opaqueproof.opaque constant_body; info : Opaqueproof.cooking_info }

type inline = bool

type 'opaque result = {
  cook_body : (constr Mod_subst.substituted, 'opaque) constant_def;
  cook_type : types;
  cook_universes : universes;
  cook_relevance : Sorts.relevance;
  cook_inline : inline;
  cook_context : Names.Id.Set.t option;
}

val cook_constant : recipe -> Opaqueproof.opaque result
val cook_constr : Opaqueproof.cooking_info list ->
  Opaqueproof.opaque_proofterm -> Opaqueproof.opaque_proofterm

val cook_inductive :
  Opaqueproof.cooking_info -> mutual_inductive_body -> mutual_inductive_body

(** {6 Utility functions used in module [Discharge]. } *)

val expmod_constr : Opaqueproof.work_list -> constr -> constr

