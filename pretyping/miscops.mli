(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Misctypes

val map_cast_type : ('a -> 'b) -> 'a cast_type -> 'b cast_type

val smartmap_cast_type : ('a -> 'a) -> 'a cast_type -> 'a cast_type

(** Printing of [intro_pattern] *)

val pr_intro_pattern : intro_pattern_expr Pp.located -> Pp.std_ppcmds
val pr_or_and_intro_pattern : or_and_intro_pattern_expr -> Pp.std_ppcmds
