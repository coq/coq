(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Tacbindings

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

