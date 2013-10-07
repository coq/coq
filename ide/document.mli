(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Based on OCaml stacks, it is the structure used by CoqIDE to represent
    the document *)

type 'a t

exception Empty
(** Alias for Stack.Empty. *)

val create : unit -> 'a t
(** Create an empty stack. *)

val push : 'a -> 'a t -> unit
(** Add an element to a stack. *)

val find : ('a -> bool -> bool) -> 'a t -> 'a
(** Find the first element satisfying the predicate.
    The boolean tells If the element is inside the focused zone.
    @raise Not_found it there is none. *)

val is_empty : 'a t -> bool
(** Whether a stack is empty. *)

val iter : ('a -> bool -> unit) -> 'a t -> unit
(** Iterate a function over elements, from the last added one. 
    The boolean tells If the element is inside the focused zone. *)

val clear : 'a t -> unit
(** Empty a stack. *)

val length : 'a t -> int
(** Length of a stack. *)

val pop  : 'a t -> 'a
(** Remove and returns the first element of the stack.
    @raise Empty if empty. *)

val tip  : 'a t -> 'a
(** Remove the first element of the stack without modifying it.
    @raise Empty if empty. *)

val to_list : 'a t -> 'a list
(** Convert to a list. *)

val find_map : ('a -> bool -> 'b option) -> 'a t -> 'b
(** Find the first element that returns [Some _].
    The boolean tells If the element is inside the focused zone.
    @raise Not_found it there is none. *)

type ('b, 'c) seek = ('b, 'c) CSig.seek = Stop of 'b | Next of 'c

(** [seek f acc s] acts like [List.fold_left f acc s] while [f] returns
    [Next acc']; it stops returning [b] as soon as [f] returns [Stop b].
    The stack is traversed from the top and is not altered.
    @raise Not_found it there is none. *)
val fold_until : ('c -> 'a -> ('b, 'c) seek) -> 'c -> 'a t -> 'b

(** After [focus s c1 c2] the top of [s] is the topmost element [x] such that
    [c1 x] is [true] and the bottom is the first element [y] following [x]
    such that [c2 y] is [true].  After a focus push/pop/top/fold_until
    only use the focused part.
    @raise Invalid_argument "CStack.focus" if there is no such [x] and [y] *)
val focus : 'a t -> cond_top:('a -> bool) -> cond_bot:('a -> bool) -> unit

(** Undoes a [focus].
    @raise Invalid_argument "CStack.unfocus" if the stack is not focused *)
val unfocus : 'a t -> unit

(** Is the stack focused *)
val focused : 'a t -> bool

(** Returns [top, s, bot] where [top @ s @ bot] is the full stack, and [s]
    the focused part *)
val to_lists : 'a t -> 'a list * 'a list * 'a list

