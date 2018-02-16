(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Declarations

(** {6 Cooking the constants. } *)

type recipe = { from : constant_body; info : Opaqueproof.cooking_info }

type inline = bool

type result = {
  cook_body : constr Mod_subst.substituted constant_def;
  cook_type : types;
  cook_universes : constant_universes;
  cook_private_univs : Univ.ContextSet.t option;
  cook_inline : inline;
  cook_context : Constr.named_context option;
}

val cook_constant : hcons:bool -> recipe -> result
val cook_constr : Opaqueproof.cooking_info -> constr -> constr

(** {6 Utility functions used in module [Discharge]. } *)

val expmod_constr : Opaqueproof.work_list -> constr -> constr

