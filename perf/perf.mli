(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Global CPU instruction counter. *)

(** [init ()] initialises, resets to 0, and starts the instruction counter. In
    case of an error, the [Failure] exception is raised, and the counter state
    is fully re-initialised so that [init] may be called again. Initialization
    is required prior to calling the [drop] and [peek] functions. *)
val init : unit -> unit

(** [drop ()] undoes the effect of [init], and frees all resources used by the
    internal state of the instruction counter. Note that the counter must have
    been initialised before calling [drop], otherwise [Failure] is raised. *)
val drop : unit -> unit

(** [peek ()] reads the value of the instruction counter, which corresponds to
    the number of instructions run by the CPU since the last (successful) call
    to [init]. Note that [Failure] is raised in case of an error, including if
    the function is called while the counter is not initialised. *)
val peek : unit -> Int64.t
