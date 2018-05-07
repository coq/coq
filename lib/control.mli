(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Global control of Coq. *)

(** Will periodically call [Thread.delay] if set to true *)
val enable_thread_delay : bool ref

val interrupt : bool ref
(** Coq interruption: set the following boolean reference to interrupt Coq
    (it eventually raises [Break], simulating a Ctrl-C) *)

val check_for_interrupt : unit -> unit
(** Use this function as a potential yield function. If {!interrupt} has been
    set, il will raise [Sys.Break]. *)

val timeout : int -> ('a -> 'b) -> 'a -> exn -> 'b
(** [timeout n f x e] tries to compute [f x], and if it fails to do so
    before [n] seconds, it raises [e] instead. *)

(** Set a particular timeout function; warning, this is an internal
   API and it is scheduled to go away. *)
type timeout = { timeout : 'a 'b. int -> ('a -> 'b) -> 'a -> exn -> 'b }
val set_timeout : timeout -> unit
