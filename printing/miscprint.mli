(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Misctypes

(** Printing of [intro_pattern] *)

val pr_intro_pattern :
  ('a -> Pp.std_ppcmds) -> 'a intro_pattern_expr Loc.located -> Pp.std_ppcmds

val pr_or_and_intro_pattern :
  ('a -> Pp.std_ppcmds) -> 'a or_and_intro_pattern_expr -> Pp.std_ppcmds

val pr_intro_pattern_naming : intro_pattern_naming_expr -> Pp.std_ppcmds

(** Printing of [move_location] *)

val pr_move_location :
  ('a -> Pp.std_ppcmds) -> 'a move_location -> Pp.std_ppcmds
