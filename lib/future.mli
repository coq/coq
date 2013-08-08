(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2013     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Futures: for now lazy computations with some purity enforcing *)
(* TODO: it may be worth separating in the type pure and inpure computations *)

exception NotReady

type 'a computation
type 'a value = [ `Val of 'a | `Exn of exn ]

(* Build a computation *)
val create : (unit -> 'a) -> 'a computation
val from_val : 'a -> 'a computation

(* Run remotely, returns the function to assign *)
val create_delegate : unit -> 'a computation * ('a value -> unit)

(* Variants to stock a copy of the current environment *)
val create_here : (unit -> 'a) -> 'a computation
val from_here : 'a -> 'a computation

(* Inspect a computation *)
val is_over : 'a computation -> bool
val is_val : 'a computation -> bool
val peek_val : 'a computation -> 'a option

(* Chain computations.
   Note that in [chain c f], f will execute in an environment modified by c
   unless ~pure:true *)
val chain :
  ?id:string -> ?pure:bool -> 'a computation -> ('a -> 'b) -> 'b computation

(* Forcing a computation *)
val force : 'a computation -> 'a
val compute : 'a computation -> 'a value

val drop : 'a computation -> 'a computation

(* Final call, no more impure chain allowed since the state is lost *)
val join : 'a computation -> 'a

(* Utility *)
val split2 : ('a * 'b) computation -> 'a computation * 'b computation
val split3 :
  ('a * 'b * 'c) computation -> 'a computation * 'b computation * 'c computation
val map2 :
  ('a computation -> 'b -> 'c) ->
     'a list computation -> 'b list -> 'c list

(* These functions are needed to get rid of side effects *)
val set_freeze : (unit -> Dyn.t) -> (Dyn.t -> unit) -> unit

(* Once set_freeze is called we can purify a computation *)
val purify : ('a -> 'b) -> 'a -> 'b

