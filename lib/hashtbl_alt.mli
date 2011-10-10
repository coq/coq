(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* The following module is a specialized version of [Hashtbl] that is
   a better space saver. Actually, [Hashcons] instanciates [Hashtbl.t]
   with [constr] used both as a key and as an image.  Thus, in each
   cell of the internal bucketlist, there are two representations of
   the same value. In this implementation, there is only one.

   Besides, the responsibility of computing the hash function is now
   given to the caller, which makes possible the interleaving of the
   hash key computation and the hash-consing. *)

module type Hashtype = sig
  type t
  val equals : t -> t -> bool
end

module type S = sig
  type elt
  (* [may_add_and_get key constr] uses [key] to look for [constr]
     in the hash table [H]. If [constr] is in [H], returns the
     specific representation that is stored in [H]. Otherwise,
     [constr] is stored in [H] and will be used as the canonical
     representation of this value in the future. *)
  val may_add_and_get : int -> elt -> elt
end

module Make (E : Hashtype) : S with type elt = E.t

module Combine : sig
  val combine : int -> int -> int
  val combinesmall : int -> int -> int
  val combine3 : int -> int -> int -> int
  val combine4 : int -> int -> int -> int -> int
end
