(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Thread safe queue with some extras *)

type 'a t
val create : unit -> 'a t
val pop : ?picky:('a -> bool) -> ?destroy:bool ref -> 'a t -> 'a
val push : 'a t -> 'a -> unit
val set_order : 'a t -> ('a -> 'a -> int) -> unit
val wait_until_n_are_waiting_and_queue_empty : int -> 'a t -> unit

(* Wake up all waiting threads *)
val broadcast : 'a t -> unit

(* Non destructive *)
val wait_until_n_are_waiting_then_snapshot : int -> 'a t -> 'a list

val clear : 'a t -> unit
val clear_saving : 'a t -> ('a -> 'b option) -> 'b list
val is_empty : 'a t -> bool

exception BeingDestroyed
(* Threads blocked in pop can get this exception if the queue is being
 * destroyed *)
val destroy : 'a t -> unit

val length : 'a t -> int
