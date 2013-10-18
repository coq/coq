(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2013     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Futures: asynchronous computations with some purity enforcing *)

exception NotReady

type 'a computation
type 'a value = [ `Val of 'a | `Exn of exn ]
type fix_exn = exn -> exn

(* Build a computation.  fix_exn is used to enrich any exception raised
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

(* Run remotely, returns the function to assign *)
type 'a assignement = [ `Val of 'a | `Exn of exn | `Comp of 'a computation]
val create_delegate : fix_exn -> 'a computation * ('a assignement -> unit)

(* Given a computation that is_exn, replace it by another one *)
val replace : 'a computation -> 'a computation -> unit

(* Inspect a computation *)
val is_over : 'a computation -> bool
val is_val : 'a computation -> bool
val is_exn : 'a computation -> bool
val peek_val : 'a computation -> 'a option

(* Chain computations.  *)
val chain : 'a computation -> ('a -> 'b) -> 'b computation

(* Forcing a computation *)
val force : 'a computation -> 'a
val compute : 'a computation -> 'a value

(* Final call, no more chain allowed since the state is lost *)
val join : 'a computation -> 'a

(* Utility *)
val split2 : ('a * 'b) computation -> 'a computation * 'b computation
val split3 :
  ('a * 'b * 'c) computation -> 'a computation * 'b computation * 'c computation
val map2 :
  ('a computation -> 'b -> 'c) ->
     'a list computation -> 'b list -> 'c list

(* Once set_freeze is called we can purify a computation *)
val purify : ('a -> 'b) -> 'a -> 'b
(* And also let a function alter the state but backtrack if it raises exn *)
val transactify : ('a -> 'b) -> 'a -> 'b

(* These functions are needed to get rid of side effects.
   Thy are set for the outermos layer of the system, since they have to
   deal with the whole system state. *)
val set_freeze : (unit -> Dyn.t) -> (Dyn.t -> unit) -> unit


