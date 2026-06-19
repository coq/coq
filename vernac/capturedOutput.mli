(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type output = Message of Feedback.level * Pp.t

(** In chronological order *)
type t = private output list

(** Build a [t] from a list in reverse chronological order. *)
val from_rev_list : output list -> t

(** Build a [t] from a list in chronological order. *)
val from_list : output list -> t

(** [vernac_assert captured flags s] checks that [captured] matches [s] according to [flags]
    ([NoDrop] is ignored and should be handled by the caller). *)
val vernac_assert : t -> Vernacexpr.AssertCapturedOutputFlags.t CAst.t list -> string CAst.t -> unit
