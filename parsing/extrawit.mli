(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Genarg
open Tacexpr

(** This file defines extra argument types *)

(** Tactics as arguments *)

val tactic_main_level : int

val rawwit_tactic : int -> (raw_tactic_expr,rlevel) abstract_argument_type
val globwit_tactic : int -> (glob_tactic_expr,glevel) abstract_argument_type
val wit_tactic : int -> (glob_tactic_expr,tlevel) abstract_argument_type

val rawwit_tactic0 : (raw_tactic_expr,rlevel) abstract_argument_type
val globwit_tactic0 : (glob_tactic_expr,glevel) abstract_argument_type
val wit_tactic0 : (glob_tactic_expr,tlevel) abstract_argument_type

val rawwit_tactic1 : (raw_tactic_expr,rlevel) abstract_argument_type
val globwit_tactic1 : (glob_tactic_expr,glevel) abstract_argument_type
val wit_tactic1 : (glob_tactic_expr,tlevel) abstract_argument_type

val rawwit_tactic2 : (raw_tactic_expr,rlevel) abstract_argument_type
val globwit_tactic2 : (glob_tactic_expr,glevel) abstract_argument_type
val wit_tactic2 : (glob_tactic_expr,tlevel) abstract_argument_type

val rawwit_tactic3 : (raw_tactic_expr,rlevel) abstract_argument_type
val globwit_tactic3 : (glob_tactic_expr,glevel) abstract_argument_type
val wit_tactic3 : (glob_tactic_expr,tlevel) abstract_argument_type

val rawwit_tactic4 : (raw_tactic_expr,rlevel) abstract_argument_type
val globwit_tactic4 : (glob_tactic_expr,glevel) abstract_argument_type
val wit_tactic4 : (glob_tactic_expr,tlevel) abstract_argument_type

val rawwit_tactic5 : (raw_tactic_expr,rlevel) abstract_argument_type
val globwit_tactic5 : (glob_tactic_expr,glevel) abstract_argument_type
val wit_tactic5 : (glob_tactic_expr,tlevel) abstract_argument_type

val is_tactic_genarg : argument_type -> bool

val tactic_genarg_level : string -> int option
