(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open EConstr
open Environ
open Evd

(** This module implements normalization by evaluation to OCaml code *)

val native_norm : env -> evar_map -> constr -> types -> constr

(** Conversion with inference of universe constraints *)
val native_infer_conv : ?pb:conv_pb -> env -> evar_map -> constr -> constr ->
  evar_map option
