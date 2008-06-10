(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Pp
open Names
open Indtypes
open Environ
open Type_errors
open Pretype_errors
open Indrec
open Cases
open Logic
(*i*)

(* This module provides functions to explain the type errors. *)

val explain_type_error : env -> type_error -> std_ppcmds

val explain_pretype_error : env -> pretype_error -> std_ppcmds

val explain_inductive_error : inductive_error -> std_ppcmds

val explain_recursion_scheme_error : recursion_scheme_error -> std_ppcmds

val explain_refiner_error : Proofview.refiner_error -> std_ppcmds

val explain_pattern_matching_error :
  env -> pattern_matching_error -> std_ppcmds

val explain_reduction_tactic_error :
  Tacred.reduction_tactic_error -> std_ppcmds
