(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** {6 States of the system} *)

(** In that module, we provide functions to get
  and set the state of the whole system. Internally, it is done by
  freezing the states of both [Lib] and [Summary]. We provide functions
  to write and restore state to and from a given file. *)

val intern_state : string -> unit
val extern_state : string -> unit

type state
val freeze : marshallable:Summary.marshallable -> state
val unfreeze : state -> unit

val summary_of_state : state -> Summary.frozen

(** {6 Rollback } *)

(** [with_state_protection f x] applies [f] to [x] and restores the
  state of the whole system as it was before applying [f] *)

val with_state_protection : ('a -> 'b) -> 'a -> 'b

(** [with_state_protection_on_exception f x] applies [f] to [x] and restores the
  state of the whole system as it was before applying [f] only if an
  exception is raised.  Unlike [with_state_protection] it also takes into
  account the proof state *)

val with_state_protection_on_exception : ('a -> 'b) -> 'a -> 'b

