(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(* Bounded stacks. If the depth is [None], then there is no depth limit. *)

type 'a t

val create : int option -> 'a t
val set_depth : 'a t -> int option -> unit
val push : 'a t -> 'a -> unit
val app_push : 'a t -> ('a -> 'a) -> unit
val app_repl : 'a t -> ('a -> 'a) -> unit
val pop : 'a t -> 'a option
val top : 'a t -> 'a option
val is_empty : 'a t -> bool
val depth : 'a t -> int
