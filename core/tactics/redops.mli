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

val make_red_flag : 'a red_atom list -> 'a glob_red_flag

val all_flags : 'a glob_red_flag

(** Mapping [red_expr_gen] *)

val map_red_expr_gen : ('a -> 'd) -> ('b -> 'e) -> ('c -> 'f) ->
  ('a,'b,'c) red_expr_gen -> ('d,'e,'f) red_expr_gen
