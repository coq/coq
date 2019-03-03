(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
