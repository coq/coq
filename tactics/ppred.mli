(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Genredexpr

val pr_evaluable_reference : Tacred.evaluable_global_reference -> Pp.t

val pr_evaluable_reference_env : Environ.env -> Tacred.evaluable_global_reference -> Pp.t

val pr_with_occurrences :
  ('a -> Pp.t) -> (string -> Pp.t) -> 'a Locus.with_occurrences -> Pp.t

val pr_short_red_flag : ('a -> Pp.t) -> 'a glob_red_flag -> Pp.t
val pr_red_flag : ('a -> Pp.t) -> 'a glob_red_flag -> Pp.t

val pr_red_expr : ('a -> Pp.t) * ('a -> Pp.t) * ('b -> Pp.t) * ('c -> Pp.t) -> (string -> Pp.t) ->
  ('a,'b,'c) red_expr_gen -> Pp.t

(** Compared to [pr_red_expr], this immediately applied the tuple
   elements to the extra arguments. *)
val pr_red_expr_env : 'env -> 'sigma ->
  ('env -> 'sigma -> 'a -> Pp.t) *
  ('env -> 'sigma -> 'a -> Pp.t) *
  ('b -> Pp.t) *
  ('env -> 'sigma -> 'c -> Pp.t) ->
  (string -> Pp.t) ->
  ('a,'b,'c) red_expr_gen -> Pp.t
