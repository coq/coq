(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This module provides functions to explain the type errors. *)

(* Used by equations *)
val explain_type_error : Environ.env -> Evd.evar_map -> Pretype_errors.type_error -> Pp.t

val explain_pretype_error : Environ.env -> Evd.evar_map -> Pretype_errors.pretype_error -> Pp.t

val explain_refiner_error : Environ.env -> Evd.evar_map -> Logic.refiner_error -> Pp.t

val explain_not_guarded : Environ.env -> Evd.evar_map ->
  (Environ.env * int * EConstr.t Type_errors.pcofix_guard_error) option ->
  (Environ.env * int * int list * EConstr.t Type_errors.pfix_guard_error) list ->
  EConstr.rec_declaration -> Pp.t
