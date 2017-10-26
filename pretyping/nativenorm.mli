(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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
  evar_map * bool
