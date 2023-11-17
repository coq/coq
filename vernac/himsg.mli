(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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

(* XXX add cases for SProp (and sort poly?) *)
type arity_error =
  | NonInformativeToInformative
  | StrongEliminationOnNonSmallType
  | WrongArity

val error_elim_explain : Sorts.family -> Sorts.family -> arity_error
(** Second argument is the familty of the inductive. *)
