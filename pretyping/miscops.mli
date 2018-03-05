(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Misctypes
open Genredexpr

(** Mapping [cast_type] *)

val map_cast_type : ('a -> 'b) -> 'a cast_type -> 'b cast_type
val smartmap_cast_type : ('a -> 'a) -> 'a cast_type -> 'a cast_type

(** Equalities on [glob_sort] *)

val glob_sort_eq : glob_sort -> glob_sort -> bool

(** Equalities on [intro_pattern_naming] *)

val intro_pattern_naming_eq :
  intro_pattern_naming_expr -> intro_pattern_naming_expr -> bool

(** Mapping [red_expr_gen] *)

val map_red_expr_gen : ('a -> 'd) -> ('b -> 'e) -> ('c -> 'f) ->
  ('a,'b,'c) red_expr_gen -> ('d,'e,'f) red_expr_gen

(** Mapping bindings *)

val map_bindings : ('a -> 'b) -> 'a bindings -> 'b bindings
val map_with_bindings : ('a -> 'b) -> 'a with_bindings -> 'b with_bindings
