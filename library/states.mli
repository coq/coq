(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** {6 States of the system} *)

(** In that module, we provide functions to get
  and set the state of the whole system. Internally, it is done by
  freezing the states of both [Lib] and [Summary]. We provide functions
  to write and restore state to and from a given file. *)

val intern_state : string -> unit
val extern_state : string -> unit

type state
val freeze : marshallable:bool -> state
val unfreeze : state -> unit

val summary_of_state : state -> Summary.frozen
val lib_of_state : state -> Lib.frozen
val replace_summary : state -> Summary.frozen -> state
val replace_lib : state -> Lib.frozen -> state

(** {6 Rollback } *)

(** [with_state_protection f x] applies [f] to [x] and restores the
  state of the whole system as it was before applying [f] *)

val with_state_protection : ('a -> 'b) -> 'a -> 'b

