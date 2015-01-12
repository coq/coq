(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Purely functional, double-ended queues *)

(** This module implements the banker's deque, from Okasaki. Most operations are
    amortized O(1). *)

type +'a t

exception Empty

(** {5 Constructor} *)

val empty : 'a t

(** The empty deque. *)

(** {5 Left-side operations} *)

val lcons : 'a -> 'a t -> 'a t
(** Pushes an element on the left side of the deque. *)

val lhd : 'a t -> 'a
(** Returns the leftmost element in the deque. Raises [Empty] when empty. *)

val ltl : 'a t -> 'a t
(** Returns the left-tail of the deque. Raises [Empty] when empty. *)

(** {5 Right-side operations} *)

val rcons : 'a -> 'a t -> 'a t
(** Same as [lcons] but on the right side. *)

val rhd : 'a t -> 'a
(** Same as [lhd] but on the right side. *)

val rtl : 'a t -> 'a t
(** Same as [ltl] but on the right side. *)

(** {5 Operations} *)

val rev : 'a t -> 'a t
(** Reverse deque. *)

val length : 'a t -> int
(** Length of a deque. *)

val is_empty : 'a t -> bool
(** Emptyness of a deque. *)

val filter : ('a -> bool) -> 'a t -> 'a t
(** Filters the deque *)
