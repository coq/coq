(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Misctypes

(** Mapping [cast_type] *)

val map_cast_type : ('a -> 'b) -> 'a cast_type -> 'b cast_type
val smartmap_cast_type : ('a -> 'a) -> 'a cast_type -> 'a cast_type

(** Equalities on [glob_sort] *)

val glob_sort_eq : glob_sort -> glob_sort -> bool

(** Equalities on [intro_pattern_naming] *)

val intro_pattern_naming_eq :
  intro_pattern_naming_expr -> intro_pattern_naming_expr -> bool
