(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Dynamics. Use with extreme care. Not for kids. *)

module type S =
sig
type 'a tag
type t = Dyn : 'a tag * 'a -> t

val create : string -> 'a tag
val eq : 'a tag -> 'b tag -> ('a, 'b) CSig.eq option
val repr : 'a tag -> string
val dump : unit -> (int * string) list
end

(** FIXME: use OCaml 4.02 generative functors when available *)
module Make(M : CSig.EmptyS) : S
