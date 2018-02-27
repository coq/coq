(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* As of OCaml 4.01.0 input_value and input do not quite work well
 * with threads.  The symptom is the following.  Two threads, each
 * of them blocked on a read (on different channels).  One is not
 * woken up even if data is available.  When the other one gets data
 * then the stuck one is eventually unblocked too.  Unix.select with
 * an unbounded wait has the same problem. *)

(* Use only the following functions on the channel *)
type thread_ic
val prepare_in_channel_for_thread_friendly_io : in_channel -> thread_ic

val thread_friendly_input_value : thread_ic -> 'a
val thread_friendly_read :
  thread_ic -> Bytes.t -> off:int -> len:int -> int
val thread_friendly_really_read :
  thread_ic -> Bytes.t -> off:int -> len:int -> unit
val thread_friendly_really_read_line : thread_ic -> string

