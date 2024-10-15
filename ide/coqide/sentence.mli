(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Retag the ends of sentences around an inserted zone *)

val tag_on_insert : GText.buffer -> unit

(** Retag the ends of sentences in the non-locked part of the buffer *)

val tag_all : GText.buffer -> unit

(** Search a sentence around some position *)

val find : GText.buffer -> GText.iter -> (GText.iter * GText.iter) option
