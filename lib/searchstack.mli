(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type 'a t
type ('a,'b) search = [ `Stop of 'b | `Cont of 'a ]

val create : unit -> 'a t
val push : 'a -> 'a t -> unit
val find : ('c -> 'a -> ('c, 'b) search) -> 'c -> 'a t -> 'b
val is_empty : 'a t -> bool
val iter : ('a -> unit) -> 'a t -> unit
val clear : 'a t -> unit
val length : 'a t -> int

(* may raise Stack.Empty *)
val pop  : 'a t -> 'a
val top  : 'a t -> 'a

(* Extra *)
val to_list : 'a t -> 'a list
