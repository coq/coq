(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Misctypes

(** Printing of [intro_pattern] *)

val pr_intro_pattern :
  ('a -> Pp.t) -> 'a intro_pattern_expr Loc.located -> Pp.t

val pr_or_and_intro_pattern :
  ('a -> Pp.t) -> 'a or_and_intro_pattern_expr -> Pp.t

val pr_intro_pattern_naming : intro_pattern_naming_expr -> Pp.t

(** Printing of [move_location] *)

val pr_move_location :
  ('a -> Pp.t) -> 'a move_location -> Pp.t

val pr_bindings :
  ('a -> Pp.t) ->
  ('a -> Pp.t) -> 'a bindings -> Pp.t

val pr_bindings_no_with :
  ('a -> Pp.t) ->
  ('a -> Pp.t) -> 'a bindings -> Pp.t

val pr_with_bindings :
  ('a -> Pp.t) ->
  ('a -> Pp.t) -> 'a * 'a bindings -> Pp.t

