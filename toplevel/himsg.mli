
(* $Id$ *)

(*i*)
open Pp
open Names
open Term
open Sign
open Environ
open Type_errors
(*i*)

(* This module provides functions to explain the various errors. *)

val explain_type_error : path_kind -> context -> type_error -> std_ppcmds

val explain_error : exn -> std_ppcmds

