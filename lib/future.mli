(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Futures: asynchronous computations.
 *
 * A Future.computation is like a lazy_t but with some extra bells and whistles
 * to deal with eventual delegation to a slave process.
 *
 * One difference with lazy_t is that a future computation that produces
 * and exception can be substituted for another computation of the same type.
 * Moreover a future computation can be delegated to another execution entity
 * that will be allowed to set the result.  Finally future computations can
 * always be marshalled: if they were joined before marshalling, they will
 * hold the computed value (assuming it is itself marshallable), otherwise
 * they will become invalid and accessing them raises a private exception.
 *)

(* Each computation has a unique id that is inherited by each offspring
 * computation (chain, split, map...).  Joined computations lose it.  *)
module UUID : sig
  type t
  val invalid : t

  val compare : t -> t -> int
  val equal : t -> t -> bool
end

module UUIDMap : Map.S with type key = UUID.t
module UUIDSet : Set.S with type elt = UUID.t

exception NotReady of string

type 'a computation
type 'a value = [ `Val of 'a | `Exn of Exninfo.iexn ]
type fix_exn = Exninfo.iexn -> Exninfo.iexn

(* Build a computation, no snapshot of the global state is taken.  If you need
   to grab a copy of the state start with from_here () and then chain.
   fix_exn is used to enrich any exception raised
   by forcing the computations or any computation that is chained after
   it. It is used by STM to attach errors to their corresponding states,
   and to communicate to the code catching the exception a valid state id. *)
val create : fix_exn -> (unit -> 'a) -> 'a computation

(* Usually from_val is used to create "fake" futures, to use the same API
   as if a real asynchronous computations was there.  In this case fixing
   the exception is not needed, but *if* the future is chained, the fix_exn
   argument should really be given *)
val from_val : ?fix_exn:fix_exn -> 'a -> 'a computation

(* Like from_val, but also takes a snapshot of the global state.  Morally
   the value is not just the 'a but also the global system state *)
val from_here : ?fix_exn:fix_exn -> 'a -> 'a computation

(* To get the fix_exn of a computation and build a Lemmas.declaration_hook.
 * When a future enters the environment a corresponding hook is run to perform
 * some work.  If this fails, then its failure has to be annotated with the
 * same state id that corresponds to the future computation end.  I.e. Qed
 * is split into two parts, the lazy one (the future) and the eager one
 * (the hook), both performing some computations for the same state id. *)
val fix_exn_of : 'a computation -> fix_exn

(* Run remotely, returns the function to assign.
   If not blocking (the default) it raises NotReady if forced before the
   delegate assigns it. *)
type 'a assignment = [ `Val of 'a | `Exn of Exninfo.iexn | `Comp of 'a computation]
val create_delegate :
  ?blocking:bool -> name:string ->
  fix_exn -> 'a computation * ('a assignment -> unit)

(* Given a computation that is_exn, replace it by another one *)
val replace : 'a computation -> 'a computation -> unit

(* Inspect a computation *)
val is_over : 'a computation -> bool
val is_val : 'a computation -> bool
val is_exn : 'a computation -> bool
val peek_val : 'a computation -> 'a option
val uuid : 'a computation -> UUID.t

(* [chain c f] chains computation [c] with [f].
 * [chain] is eager, that is to say, it won't suspend the new computation
 * if the old one is_over (Exn or Val).
*)
val chain : 'a computation -> ('a -> 'b) -> 'b computation

(* Forcing a computation *)
val force : 'a computation -> 'a
val compute : 'a computation -> 'a value

(* Final call.
 * Also the fix_exn function is lost, hence error reporting can be incomplete
 * in a computation obtained by chaining on a joined future. *)
val join : 'a computation -> 'a

(* Call this before stocking the future.  If it is_val then it is joined *)
val sink : 'a computation -> unit

(*** Utility functions ************************************************* ***)
val split2 :
  ('a * 'b) computation -> 'a computation * 'b computation
val map2 :
  ('a computation -> 'b -> 'c) ->
     'a list computation -> 'b list -> 'c list

(** Debug: print a computation given an inner printing function. *)
val print : ('a -> Pp.t) -> 'a computation -> Pp.t

val customize_not_ready_msg : (string -> Pp.t) -> unit
val customize_not_here_msg : (string -> Pp.t) -> unit
