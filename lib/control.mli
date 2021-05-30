(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Global control of Coq. *)

(** Used to convert signals to exceptions *)
exception Timeout

(** Will periodically call [Thread.delay] if set to true *)
val enable_thread_delay : bool ref

val interrupt : bool ref
(** Coq interruption: set the following boolean reference to interrupt Coq
    (it eventually raises [Break], simulating a Ctrl-C) *)

val check_for_interrupt : unit -> unit
(** Use this function as a potential yield function. If {!interrupt} has been
    set, il will raise [Sys.Break]. *)

val timeout : float -> ('a -> 'b) -> 'a -> 'b option
(** [timeout n f x] tries to compute [Some (f x)], and if it fails to do so
    before [n] seconds, returns [None] instead. *)

(** Set a particular timeout function; warning, this is an internal
   API and it is scheduled to go away. *)
type timeout = { timeout : 'a 'b. float -> ('a -> 'b) -> 'a -> 'b option }
val set_timeout : timeout -> unit

(** [protect_sigalrm f x] computes [f x], but if SIGALRM is received during that
    computation, the signal handler is executed only once the computation is
    terminated. Otherwise said, it makes the execution of [f] atomic w.r.t.
    handling of SIGALRM.

    This is useful for example to prevent the implementation of `Timeout` to
    interrupt I/O routines, generating ill-formed output.

*)
val protect_sigalrm : ('a -> 'b) -> 'a -> 'b
