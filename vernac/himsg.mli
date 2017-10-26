(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Indtypes
open Environ
open Type_errors
open Pretype_errors
open Typeclasses_errors
open Indrec
open Cases
open Logic

(** This module provides functions to explain the type errors. *)

val explain_type_error : env -> Evd.evar_map -> type_error -> Pp.t

val explain_pretype_error : env -> Evd.evar_map -> pretype_error -> Pp.t

val explain_inductive_error : inductive_error -> Pp.t

val explain_typeclass_error : env -> typeclass_error -> Pp.t

val explain_recursion_scheme_error : recursion_scheme_error -> Pp.t

val explain_refiner_error : refiner_error -> Pp.t

val explain_pattern_matching_error :
  env -> Evd.evar_map -> pattern_matching_error -> Pp.t

val explain_reduction_tactic_error :
  Tacred.reduction_tactic_error -> Pp.t

val explain_module_error : Modops.module_typing_error -> Pp.t

val explain_module_internalization_error :
  Modintern.module_internalization_error -> Pp.t

val map_pguard_error : ('c -> 'd) -> 'c pguard_error -> 'd pguard_error
val map_ptype_error : ('c -> 'd) -> ('c, 'c) ptype_error -> ('d, 'd) ptype_error
