(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Declarations
open Environ
open Univ

(** {6 Cooking the constants. } *)

type work_list = Id.t array Cmap.t * Id.t array Mindmap.t

type recipe = {
  d_from : constant_body;
  d_abstract : Context.named_context;
  d_modlist : work_list }

type inline = bool

type result =
  constant_def * constant_type * constant_constraints * inline
    * Context.section_context option

val cook_constant : env -> recipe -> result

(** {6 Utility functions used in module [Discharge]. } *)

val expmod_constr : work_list -> constr -> constr

