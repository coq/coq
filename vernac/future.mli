(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

type fix_exn = Stateid.exn_info option

(* Build a computation, no snapshot of the global state is taken.  If you need
   to grab a copy of the state start with from_here () and then chain.
   fix_exn is used to enrich any exception raised
   by forcing the computations or any computation that is chained after
   it. It is used by STM to attach errors to their corresponding states,
   and to communicate to the code catching the exception a valid state id. *)
val create : fix_exn:fix_exn -> (unit -> 'a) -> 'a computation

(* Usually from_val is used to create "fake" futures, to use the same API
   as if a real asynchronous computations was there. *)
val from_val : 'a -> 'a computation

(* Run remotely, returns the function to assign.
   If not blocking (the default) it raises NotReady if forced before the
   delegate assigns it. *)
type 'a assignment = [ `Val of 'a | `Exn of Exninfo.iexn | `Comp of (unit -> 'a)]
val create_delegate :
  ?blocking:bool -> name:string ->
  fix_exn -> 'a computation * ('a assignment -> unit)

(* Given a computation that is_exn, replace it by another one *)
val replace : 'a computation -> 'a computation -> unit

(* Inspect a computation *)
val is_over : 'a computation -> bool
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

(** Debug: print a computation given an inner printing function. *)
val print : ('a -> Pp.t) -> 'a computation -> Pp.t
