(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Names
open Indtypes
open Environ
open Type_errors
open Pretype_errors
open Typeclasses_errors
open Indrec
open Cases
open Logic

(** This module provides functions to explain the type errors. *)

val explain_type_error : env -> Evd.evar_map -> type_error -> std_ppcmds

val explain_pretype_error : env -> Evd.evar_map -> pretype_error -> std_ppcmds

val explain_inductive_error : inductive_error -> std_ppcmds

val explain_typeclass_error : env -> typeclass_error -> Pp.std_ppcmds

val explain_recursion_scheme_error : recursion_scheme_error -> std_ppcmds

val explain_refiner_error : refiner_error -> std_ppcmds

val explain_pattern_matching_error :
  env -> pattern_matching_error -> std_ppcmds

val explain_reduction_tactic_error :
  Tacred.reduction_tactic_error -> std_ppcmds

val explain_ltac_call_trace :
  int * Proof_type.ltac_call_kind * Proof_type.ltac_trace * Pp.loc ->
  std_ppcmds

val explain_module_error : Modops.module_typing_error -> std_ppcmds

val explain_module_internalization_error :
  Modintern.module_internalization_error -> std_ppcmds
