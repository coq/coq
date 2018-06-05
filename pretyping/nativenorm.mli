(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open EConstr
open Environ
open Evd

(** This module implements normalization by evaluation to OCaml code *)

val get_profile_filename : unit -> string
val set_profile_filename : string -> unit

val get_profiling_enabled : unit -> bool
val set_profiling_enabled : bool -> unit


val native_norm : env -> evar_map -> constr -> types -> constr

(** Conversion with inference of universe constraints *)
val native_infer_conv : ?pb:conv_pb -> env -> evar_map -> constr -> constr ->
  evar_map option
