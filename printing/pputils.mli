(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Genarg
open Misctypes
open Locus
open Genredexpr

val pr_located : ('a -> std_ppcmds) -> 'a Loc.located -> std_ppcmds
(** Prints an object surrounded by its commented location *)

val pr_or_var : ('a -> std_ppcmds) -> 'a or_var -> std_ppcmds
val pr_or_by_notation : ('a -> std_ppcmds) -> 'a or_by_notation -> std_ppcmds
val pr_with_occurrences :
  ('a -> std_ppcmds) -> (string -> std_ppcmds) -> 'a with_occurrences -> std_ppcmds

val pr_short_red_flag : ('a -> std_ppcmds) -> 'a glob_red_flag -> std_ppcmds
val pr_red_flag : ('a -> std_ppcmds) -> 'a glob_red_flag -> std_ppcmds
val pr_red_expr :
  ('a -> std_ppcmds) * ('a -> std_ppcmds) * ('b -> std_ppcmds) * ('c -> std_ppcmds) ->
  (string -> std_ppcmds) ->
  ('a,'b,'c) red_expr_gen -> std_ppcmds

val pr_raw_generic : Environ.env -> rlevel generic_argument Genprint.printer
val pr_glb_generic : Environ.env -> glevel generic_argument Genprint.printer
