(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** The Coq toplevel loop. *)

(** A buffer for the character read from a channel. We store the command
 * entered to be able to report errors without pretty-printing. *)

type input_buffer = {
  mutable prompt : unit -> string;
  mutable str : Bytes.t; (** buffer of already read characters *)
  mutable len : int;    (** number of chars in the buffer *)
  mutable bols : int list; (** offsets in str of begining of lines *)
  mutable tokens : Pcoq.Gram.coq_parsable; (** stream of tokens *)
  mutable start : int } (** stream count of the first char of the buffer *)

(** The input buffer of stdin. *)

val top_buffer : input_buffer
val set_prompt : (unit -> string) -> unit

(** Toplevel feedback printer. *)
val coqloop_feed : Feedback.feedback -> unit

(** Parse and execute one vernac command. *)

val do_vernac : Stateid.t -> Stateid.t

(** Main entry point of Coq: read and execute vernac commands. *)

val loop : unit -> unit
