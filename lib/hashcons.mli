(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Generic hash-consing. *)

module type Comp =
  sig
    type t
    type u
    val hash_sub :  u -> t -> t
    val equal : t -> t -> bool
    val hash : t -> int
  end

module type S =
  sig
    type t
    type u
    val f : unit -> (u -> t -> t)
  end

module Make(X:Comp) : (S with type t = X.t and type u = X.u)

val simple_hcons : (unit -> 'u -> 't -> 't) -> ('u -> 't -> 't)
val recursive_hcons : (unit -> ('t -> 't) * 'u -> 't -> 't) -> ('u -> 't -> 't)
val recursive_loop_hcons :
    (unit -> ('t -> 't) * 'u -> 't -> 't) -> ('u -> 't -> 't)
val recursive2_hcons :
  (unit -> ('t1 -> 't1) * ('t2 -> 't2) * 'u1 -> 't1 -> 't1) ->
    (unit -> ('t1 -> 't1) * ('t2 -> 't2) * 'u2 -> 't2 -> 't2) ->
      'u1 -> 'u2 -> ('t1 -> 't1) * ('t2 -> 't2)

(** Declaring and reinitializing global hash-consing functions *)

val init : unit -> unit
val register_hcons : ('u -> 't -> 't) -> ('u -> 't -> 't)

module Hstring : (S with type t = string and type u = unit)
module Hobj : (S with type t = Obj.t and type u = (Obj.t -> Obj.t) * unit)

val string : string -> string
val obj : Obj.t -> Obj.t

val magic_hash : 'a -> 'a

