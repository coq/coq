(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(* The type of editors.
 * An editor is a finite map, ['a -> 'b], which knows how to apply
 * modification functions to the value in the range, and how to
 * focus on a member of the range.
 * It also supports the notion of a limited-depth undo, and that certain
 * modification actions do not push onto the undo stack, since they are
 * reversible. *)

type ('a,'b,'c) t

val empty : unit -> ('a,'b,'c) t

(* sets the focus to the specified domain element *)
val focus : ('a,'b,'c) t -> 'a -> unit

(* unsets the focus which must not already be unfocused *)
val unfocus : ('a,'b,'c) t -> unit

(* gives the last focused element or [None] if none *)
val last_focused : ('a,'b,'c) t -> 'a option

(* are we focused ? *)
val focusedp : ('a,'b,'c) t -> bool

(* If we are focused, then return the current domain,range pair. *)
val read : ('a,'b,'c) t -> ('a * 'b * 'c) option

(* mutates the currently-focused range element, pushing its
 * old value onto the undo stack
 *)
val mutate : ('a,'b,'c) t -> ('c -> 'b -> 'b) -> unit

(* mutates the currently-focused range element, in place. *)
val rev_mutate : ('a,'b,'c) t -> ('c -> 'b -> 'b) -> unit

(* Pops the specified number of elements off of the undo stack, *
  reinstating the last popped element. The undo stack is independently
  managed for each range element. *)
val undo : ('a,'b,'c) t -> int -> unit

val create : ('a,'b,'c) t -> 'a * 'b * 'c * int option -> unit
val delete : ('a,'b,'c) t -> 'a -> unit

val dom : ('a,'b,'c) t -> 'a list

val clear : ('a,'b,'c) t -> unit
