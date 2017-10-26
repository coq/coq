(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Genarg
open Misctypes
open Locus
open Genredexpr

val pr_located : ('a -> Pp.t) -> 'a Loc.located -> Pp.t
(** Prints an object surrounded by its commented location *)

val pr_or_var : ('a -> Pp.t) -> 'a or_var -> Pp.t
val pr_or_by_notation : ('a -> Pp.t) -> 'a or_by_notation -> Pp.t
val pr_with_occurrences :
  ('a -> Pp.t) -> (string -> Pp.t) -> 'a with_occurrences -> Pp.t

val pr_short_red_flag : ('a -> Pp.t) -> 'a glob_red_flag -> Pp.t
val pr_red_flag : ('a -> Pp.t) -> 'a glob_red_flag -> Pp.t
val pr_red_expr :
  ('a -> Pp.t) * ('a -> Pp.t) * ('b -> Pp.t) * ('c -> Pp.t) ->
  (string -> Pp.t) ->
  ('a,'b,'c) red_expr_gen -> Pp.t

val pr_raw_generic : Environ.env -> rlevel generic_argument -> Pp.t
val pr_glb_generic : Environ.env -> glevel generic_argument -> Pp.t
