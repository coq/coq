(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Platform-specific Implementation of a global instruction counter. *)

(** [read_counter ()] returns the current value of the instruction counter, or
    an error message indicating why it could not be obtained. Note that counts
    returned by this function are not meaningful in absolute terms. To measure
    how many instructions it takes to run a piece of code, read the counter at
    the start and at the end, and compute the difference. *)
val read_counter : unit -> (Int64.t, string) Result.t
