
(* $Id$ *)

(*i*)
open Pp
open Names
open Inductive
open Sign
open Type_errors
(*i*)

(* This module provides functions to explain the type errors. *)

val explain_type_error : path_kind -> context -> type_error -> std_ppcmds

val explain_inductive_error : inductive_error -> std_ppcmds
