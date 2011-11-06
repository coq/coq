(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*s States of the system. In that module, we provide functions to get
  and set the state of the whole system. Internally, it is done by
  freezing the states of both [Lib] and [Summary]. We provide functions
  to write and restore state to and from a given file. *)

val intern_state : string -> unit
val extern_state : string -> unit

type state
val freeze : unit -> state
val unfreeze : state -> unit

(*s Rollback. [with_heavy_rollback f x] applies [f] to [x] and restores the
  state of the whole system as it was before the evaluation if an exception
  is raised. *)

val with_heavy_rollback : ('a -> 'b) -> (exn -> exn) -> 'a -> 'b

(*s [with_state_protection f x] applies [f] to [x] and restores the
  state of the whole system as it was before the evaluation of f *)

val with_state_protection : ('a -> 'b) -> 'a -> 'b


