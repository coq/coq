(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Extended interface for OCaml stacks. *)

type 'a t

exception Empty
(** Alias for Stack.Empty. *)

val create : unit -> 'a t
(** Create an empty stack. *)

val push : 'a -> 'a t -> unit
(** Add an element to a stack. *)

val find : ('a -> bool) -> 'a t -> 'a
(** Find the first element satisfying the predicate.
    @raise Not_found it there is none. *)

val is_empty : 'a t -> bool
(** Whether a stack is empty. *)

val iter : ('a -> unit) -> 'a t -> unit
(** Iterate a function over elements, from the last added one. *)

val clear : 'a t -> unit
(** Empty a stack. *)

val length : 'a t -> int
(** Length of a stack. *)

val pop  : 'a t -> 'a
(** Remove and returns the first element of the stack.
    @raise Empty if empty. *)

val top  : 'a t -> 'a
(** Remove the first element of the stack without modifying it.
    @raise Empty if empty. *)

val to_list : 'a t -> 'a list
(** Convert to a list. *)

val find_map : ('a -> 'b option) -> 'a t -> 'b
(** Find the first element that returns [Some _].
    @raise Not_found it there is none. *)

val fold_until : ('c -> 'a -> 'c CSig.until) -> 'c -> 'a t -> 'c
(** Like CList.fold_left_until.
    The stack is traversed from the top and is not altered. *)

