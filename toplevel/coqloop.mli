(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The Rocq toplevel loop. *)

(** A buffer for the character read from a channel. We store the command
 * entered to be able to report errors without pretty-printing. *)

type input_buffer

(** The input buffer of stdin. *)

val top_buffer : input_buffer
val set_prompt : (unit -> string) -> unit

(** Toplevel feedback printer. *)
val coqloop_feed : Feedback.feedback -> unit

(** State tracked while in the OCaml toplevel *)
val ml_toplevel_state : Vernac.State.t option ref

(** Whether the "include" file was already run at least once *)
val ml_toplevel_include_ran : bool ref

(** The main loop *)
val loop : state:Vernac.State.t -> Vernac.State.t

(** Main entry point of Rocq: read and execute vernac commands. *)
val run : opts:Coqargs.t -> state:Vernac.State.t -> unit
