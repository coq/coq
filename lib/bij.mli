(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(* Bijections. *)

type ('a,'b) t

val empty : ('a,'b) t
val map : ('a,'b) t -> 'a -> 'b
val pam : ('a,'b) t -> 'b -> 'a
val dom : ('a,'b) t -> 'a list
val rng : ('a,'b) t -> 'b list
val in_dom : ('a,'b) t -> 'a -> bool
val in_rng : ('a,'b) t -> 'b -> bool
val app : ('a -> 'b -> unit) -> ('a,'b) t -> unit
val to_list : ('a,'b) t -> ('a * 'b) list

val add : ('a,'b) t -> 'a * 'b -> ('a,'b) t
val remove : ('a,'b) t -> 'a -> ('a,'b) t
