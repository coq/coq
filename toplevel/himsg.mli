
(*i $Id$ i*)

(*i*)
open Pp
open Names
open Indtypes
open Environ
open Type_errors
open Logic
(*i*)

(* This module provides functions to explain the type errors. *)

val explain_type_error : path_kind -> env -> type_error -> std_ppcmds

val explain_inductive_error : inductive_error -> std_ppcmds

val explain_refiner_error : refiner_error -> std_ppcmds
