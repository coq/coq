(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val infer_inductive : Environ.env -> Entries.mutual_inductive_entry ->
  Entries.mutual_inductive_entry
(** If the entry has non-[None] [mind_entry_variance] then it is reinferred from scratch.
    Otherwise this function is a noop. *)

val dummy_variance : Entries.universe_entry -> Univ.Variance.t array
(** Convenient way to produce a valid [mind_entry_variance] in
   anticipation of passing it to [infer_inductive]. *)
