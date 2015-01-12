(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Global control of Coq. *)

val interrupt : bool ref
(** Coq interruption: set the following boolean reference to interrupt Coq
    (it eventually raises [Break], simulating a Ctrl-C) *)

val check_for_interrupt : unit -> unit
(** Use this function as a potential yield function. If {!interrupt} has been
    set, il will raise [Sys.Break]. *)

val timeout : int -> (unit -> 'a) -> exn -> 'a
(** [timeout n f e] tries to compute [f], and if it fails to do so before [n]
    seconds, it raises [e] instead. *)

type timeout = { timeout : 'a. int -> (unit -> 'a) -> exn -> 'a }

val set_timeout : timeout -> unit
(** Set a particular timeout function. *)
