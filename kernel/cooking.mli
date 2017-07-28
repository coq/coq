(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Declarations
open Environ

(** {6 Cooking the constants. } *)

type recipe = { from : constant_body; info : Opaqueproof.cooking_info }

type inline = bool

type result = {
  cook_body : constant_def;
  cook_type : constant_type;
  cook_proj : projection_body option;
  cook_universes : constant_universes;
  cook_inline : inline;
  cook_context : Context.Named.t option;
}

val cook_constant : hcons:bool -> env -> recipe -> result
val cook_constr : Opaqueproof.cooking_info -> Term.constr -> Term.constr

(** {6 Utility functions used in module [Discharge]. } *)

val expmod_constr : Opaqueproof.work_list -> constr -> constr

