(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Tries. This module implements a data structure [('a,'b) t] mapping lists
   of values of type ['a] to sets (as lists) of values of type ['b]. *)

type ('a,'b) t

val empty : ('a,'b) t

(** Work on labels, not on paths. *)

val map : ('a,'b) t -> 'a -> ('a,'b) t
val xtract : ('a,'b) t -> 'b list
val dom : ('a,'b) t -> 'a list
val in_dom : ('a,'b) t -> 'a -> bool

(** Work on paths, not on labels. *)

val add : ('a,'b) t -> 'a list * 'b -> ('a,'b) t
val rmv : ('a,'b) t -> ('a list * 'b) -> ('a,'b) t

val app : (('a list * 'b) -> unit) -> ('a,'b) t -> unit
val to_list : ('a,'b) t -> ('a list * 'b) list

