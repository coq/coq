(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(* Bounded stacks. If the depth is [None], then there is no depth limit. *)

type 'a t

val create : int -> 'a -> 'a t
val push : 'a t -> 'a -> unit
val app_push : 'a t -> ('a -> 'a) -> unit
val app_repl : 'a t -> ('a -> 'a) -> unit
val pop : 'a t -> unit
val top : 'a t -> 'a
val depth : 'a t -> int
