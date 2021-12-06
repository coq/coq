(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Tactypes

(** Printing of [intro_pattern] *)

val pr_intro_pattern :
  ('a -> Pp.t) -> ('b -> Pp.t) -> ('a,'b) intro_pattern_expr CAst.t -> Pp.t

val pr_or_and_intro_pattern :
  ('a -> Pp.t) -> ('b -> Pp.t) -> ('a,'b) or_and_intro_pattern_expr -> Pp.t

val pr_intro_pattern_naming : Namegen.intro_pattern_naming_expr -> Pp.t

(** Printing of [move_location] *)

val pr_bindings :
  ('a -> Pp.t) ->
  ('a -> Pp.t) -> 'a bindings -> Pp.t

val pr_bindings_no_with :
  ('a -> Pp.t) ->
  ('a -> Pp.t) -> 'a bindings -> Pp.t

val pr_with_bindings :
  ('a -> Pp.t) ->
  ('a -> Pp.t) -> 'a * 'a bindings -> Pp.t

