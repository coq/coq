(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Pp
open Names
open Indtypes
open Environ
open Type_errors
open Pretype_errors
open Cases
open Logic
open Term
(*i*)

(* This module provides functions to explain the type errors. *)

val explain_type_error : env -> type_error -> std_ppcmds

val explain_pretype_error : env -> pretype_error -> std_ppcmds

val explain_inductive_error : inductive_error -> std_ppcmds

val explain_refiner_error : refiner_error -> std_ppcmds

val explain_pattern_matching_error :
  env -> pattern_matching_error -> std_ppcmds

val explain_symbol_error : symbol_error -> std_ppcmds

val explain_rule_error : (constr * constr) -> env -> env -> rule_error
  -> std_ppcmds

val explain_condition_error : condition_error -> std_ppcmds

