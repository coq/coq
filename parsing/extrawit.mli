(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Genarg
open Tacexpr

(** This file defines extra argument types *)

(** Tactics as arguments *)

val tactic_main_level : int

val wit_tactic : int -> (raw_tactic_expr, glob_tactic_expr, glob_tactic_expr) genarg_type

val wit_tactic0 : (raw_tactic_expr, glob_tactic_expr, glob_tactic_expr) genarg_type
val wit_tactic1 : (raw_tactic_expr, glob_tactic_expr, glob_tactic_expr) genarg_type
val wit_tactic2 : (raw_tactic_expr, glob_tactic_expr, glob_tactic_expr) genarg_type
val wit_tactic3 : (raw_tactic_expr, glob_tactic_expr, glob_tactic_expr) genarg_type
val wit_tactic4 : (raw_tactic_expr, glob_tactic_expr, glob_tactic_expr) genarg_type
val wit_tactic5 : (raw_tactic_expr, glob_tactic_expr, glob_tactic_expr) genarg_type

val is_tactic_genarg : argument_type -> bool

val tactic_genarg_level : string -> int option
