(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file defines the datatypes used as internal states by the
    tactic monad, and specialises the [Logic_monad] to these types. It should
    not be used directly. Consider using {!Proofview} instead. *)

(** {6 Traces} *)

module Trace : sig

  (** The intent is that an ['a forest] is a list of messages of type
      ['a]. But messages can stand for a list of more precise
      messages, hence the structure is organised as a tree. *)
  type 'a forest = 'a tree list
  and  'a tree   = Seq of 'a * 'a forest

  (** To build a trace incrementally, we use an intermediary data
      structure on which we can define an S-expression like language
      (like a simplified xml except the closing tags do not carry a
      name). *)
  type 'a incr
  val to_tree : 'a incr -> 'a forest

  (** [open a] opens a tag with name [a]. *)
  val opn : 'a -> 'a incr -> 'a incr

  (** [close] closes the last open tag. It is the responsibility of
      the user to close all the tags. *)
  val close : 'a incr -> 'a incr

  (** [leaf] creates an empty tag with name [a]. *)
  val leaf : 'a -> 'a incr -> 'a incr

end

(** {6 State types} *)

(** We typically label nodes of [Trace.tree] with messages to
    print. But we don't want to compute the result. *)
type lazy_msg = unit -> Pp.t

(** Info trace. *)
module Info : sig

  (** The type of the tags for [info]. *)
  type tag =
    | Msg of lazy_msg (** A simple message *)
    | Tactic of lazy_msg (** A tactic call *)
    | Dispatch  (** A call to [tclDISPATCH]/[tclEXTEND] *)
    | DBranch  (** A special marker to delimit individual branch of a dispatch. *)

  type state = tag Trace.incr
  type tree = tag Trace.forest

  val print : tree -> Pp.t

  (** [collapse n t] flattens the first [n] levels of [Tactic] in an
      info trace, effectively forgetting about the [n] top level of
      names (if there are fewer, the last name is kept). *)
  val collapse : int -> tree -> tree

end

module StateStore : Store.S
type goal = Evar.t
type goal_with_state
val drop_state : goal_with_state -> goal
val get_state : goal_with_state -> StateStore.t
val goal_with_state : goal -> StateStore.t -> goal_with_state
val with_empty_state : goal -> goal_with_state
val map_goal_with_state : (goal -> goal) -> goal_with_state -> goal_with_state

(** Type of proof views: current [evar_map] together with the list of
    focused goals. *)
type proofview = {
  solution : Evd.evar_map;
  comb : goal_with_state list;
  shelf : goal list;
}

(** {6 Instantiation of the logic monad} *)

module P : sig
  type s = proofview * Environ.env

  (** Status (safe/unsafe) * given up *)
  type w = bool * goal list

  val wunit : w
  val wprod : w -> w -> w

  (** Recording info trace (true) or not. *)
  type e = bool

  type u = Info.state

  val uunit : u
end

module Logical : module type of Logic_monad.Logical(P)


(** {6 Lenses to access to components of the states} *)

module type State = sig
  type t
  val get : t Logical.t
  val set : t -> unit Logical.t
  val modify : (t->t) -> unit Logical.t
end

module type Writer = sig
  type t
  val put : t -> unit Logical.t
end

(** Lens to the [proofview]. *)
module Pv : State with type t := proofview

(** Lens to the [evar_map] of the proofview. *)
module Solution : State with type t := Evd.evar_map

(** Lens to the list of focused goals. *)
module Comb : State with type t = goal_with_state list

(** Lens to the global environment. *)
module Env : State with type t := Environ.env

(** Lens to the tactic status ([true] if safe, [false] if unsafe) *)
module Status : Writer with type t := bool

(** Lens to the list of goals which have been shelved during the
    execution of the tactic. *)
module Shelf : State with type t = goal list

(** Lens to the list of goals which were given up during the execution
    of the tactic. *)
module Giveup : Writer with type t = goal list

(** Lens and utilies pertaining to the info trace *)
module InfoL : sig
  (** [record_trace t] behaves like [t] and compute its [info] trace. *)
  val record_trace : 'a Logical.t -> 'a Logical.t

  val update : (Info.state -> Info.state) -> unit Logical.t
  val opn : Info.tag -> unit Logical.t
  val close : unit Logical.t
  val leaf : Info.tag -> unit Logical.t

  (** [tag a t] opens tag [a] runs [t] then closes the tag. *)
  val tag : Info.tag -> 'a Logical.t -> 'a Logical.t
end
