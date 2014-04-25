(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2013     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Futures: asynchronous computations with some purity enforcing
 *
 * A Future.computation is like a lazy_t but with some extra bells and whistles
 * to deal with imperative code and eventual delegation to a slave process.
 *
 * Example of a simple scenario taken into account:
 *
 *   let f = Future.from_here (number_of_constants (Global.env())) in
 *   let g = Future.chain ~pure:false f (fun n ->
 *             n = number_of_constants (Global.env())) in
 *   ...
 *   Lemmas.save_named ...;
 *   ...
 *   let b = Future.force g in
 *
 * The Future.computation f holds a (immediate, no lazy here) value.
 * We then chain to obtain g that (will) hold false if (when it will be
 * run) the global environment has a different number of constants, true
 * if nothing changed.
 * Before forcing g, we add to the global environment one more constant.
 * When finally we force g.  Its value is going to be *true*.
 * This because Future.from_here stores in the computation not only the initial
 * value but the entire system state.  When g is forced the state is restored,
 * hence Global.env() returns the environment that was actual when f was
 * created.
 * Last, forcing g is run protecting the system state, hence when g finishes,
 * the actual system state is restored.
 *
 * If you compare this with lazy_t, you see that the value returned is *false*,
 * that is counter intuitive and error prone.
 *
 * Still not all computations are impure and acess/alter the system state.
 * This class can be optimized by using ~pure:true, but there is no way to
 * statically check if this flag is misused, hence use it with care.
 *
 * Other differences with lazy_t is that a future computation that produces
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

exception NotReady

type 'a computation
type 'a value = [ `Val of 'a | `Exn of exn ]
type fix_exn = exn -> exn

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

(* Run remotely, returns the function to assign.  Optionally tekes a function
   that is called when forced.  The default one is to raise NotReady.
   The assignement function does not change the uuid. *)
type 'a assignement = [ `Val of 'a | `Exn of exn | `Comp of 'a computation]
val create_delegate :
  ?force:(unit -> 'a assignement) ->
  fix_exn -> 'a computation * ('a assignement -> unit)

(* Given a computation that is_exn, replace it by another one *)
val replace : 'a computation -> 'a computation -> unit

(* Inspect a computation *)
val is_over : 'a computation -> bool
val is_val : 'a computation -> bool
val is_exn : 'a computation -> bool
val peek_val : 'a computation -> 'a option
val uuid : 'a computation -> UUID.t

(* [chain greedy pure c f] chains computation [c] with [f].
 * The [greedy] and [pure] parameters are tricky:
 * [pure]:
 *   When pure is true, the returned computation will not keep a copy
 *   of the global state.
 *   [let c' = chain ~pure:true c f in let c'' = chain ~pure:false c' g in]
 *   is invalid.  It works if one forces [c''] since the whole computation
 *   will be executed in one go.  It will not work, and raise an anomaly, if
 *   one forces c' and then c''.
 *   [join c; chain ~pure:false c g] is invalid and fails at runtime.
 *   [force c; chain ~pure:false c g] is correct.
 * [greedy]:
 *   The [greedy] parameter forces immediately the new computation if
 *   the old one is_over (Exn or Val). Defaults to true. *)
val chain : ?greedy:bool -> pure:bool ->
  'a computation -> ('a -> 'b) -> 'b computation

(* Forcing a computation *)
val force : 'a computation -> 'a
val compute : 'a computation -> 'a value

(* Final call, no more *inpure* chain allowed since the state is lost.
 * Also the fix_exn function is lost, hence error reporting can be incomplete
 * in a computation obtained by chaining on a joined future. *)
val join : 'a computation -> 'a

(* Call this before stocking the future.  If it is_val then it is joined *)
val sink : 'a computation -> unit

(*** Utility functions ************************************************* ***)
val split2 : ?greedy:bool ->
  ('a * 'b) computation -> 'a computation * 'b computation
val map2 : ?greedy:bool ->
  ('a computation -> 'b -> 'c) ->
     'a list computation -> 'b list -> 'c list

(* Once set_freeze is called we can purify a computation *)
val purify : ('a -> 'b) -> 'a -> 'b
(* And also let a function alter the state but backtrack if it raises exn *)
val transactify : ('a -> 'b) -> 'a -> 'b

(** Debug: print a computation given an inner printing function. *)
val print : ('a -> Pp.std_ppcmds) -> 'a computation -> Pp.std_ppcmds

(* These functions are needed to get rid of side effects.
   Thy are set for the outermos layer of the system, since they have to
   deal with the whole system state. *)
val set_freeze : (unit -> Dyn.t) -> (Dyn.t -> unit) -> unit
