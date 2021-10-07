(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The Coq toplevel loop. *)

(** A buffer for the character read from a channel. We store the command
 * entered to be able to report errors without pretty-printing. *)

type input_buffer = {
  mutable prompt : Stm.doc -> string;
  mutable str : Bytes.t; (** buffer of already read characters *)
  mutable len : int;    (** number of chars in the buffer *)
  mutable bols : int list; (** offsets in str of beginning of lines *)
  mutable tokens : Pcoq.Parsable.t; (** stream of tokens *)
  mutable start : int } (** stream count of the first char of the buffer *)

(** The input buffer of stdin. *)

val top_buffer : input_buffer
val set_prompt : (unit -> string) -> unit

(** Toplevel feedback printer. *)
val coqloop_feed : Feedback.feedback -> unit

(** Last document seen after `Drop` *)
val drop_last_doc : Vernac.State.t option ref
val drop_args : Coqargs.t option ref

(** Main entry point of Coq: read and execute vernac commands. *)
val loop : opts:Coqargs.t -> state:Vernac.State.t -> unit
