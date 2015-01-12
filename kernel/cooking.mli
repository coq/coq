(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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

type result =
  constant_def * constant_type * projection_body option * 
    bool * constant_universes * inline
    * Context.section_context option

val cook_constant : env -> recipe -> result
val cook_constr : Opaqueproof.cooking_info -> Term.constr -> Term.constr

(** {6 Utility functions used in module [Discharge]. } *)

val expmod_constr : Opaqueproof.work_list -> constr -> constr

