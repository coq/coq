(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
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

module type EqType = sig
  type t
  val equal : t -> t -> bool
end

module type S = sig
  type elt
  type t
  val create : int -> t
  val repr : int -> elt -> t -> elt
end

module Make (E : EqType) =
  struct

    type elt = E.t

    type bucketlist = Empty | Cons of elt * int * bucketlist

    type t = {
      mutable size : int;
      mutable data : bucketlist array; }

    let create s =
      let s = min (max 1 s) Sys.max_array_length in
      { size = 0; data = Array.make s Empty }

    let resize table =
      let odata = table.data in
      let osize = Array.length odata in
      let nsize = min (2 * osize + 1) Sys.max_array_length in
      if nsize <> osize then begin
        let ndata = Array.create nsize Empty in
        let rec insert_bucket = function
        | Empty -> ()
        | Cons (key, hash, rest) ->
            let nidx = hash mod nsize in
            let obucket = ndata.(nidx) in
            ndata.(nidx) <- Cons (key, hash, obucket);
            insert_bucket rest
        in
        for i = 0 to osize - 1 do insert_bucket odata.(i) done;
        table.data <- ndata
      end

  let add hash key table =
    let odata = table.data in
    let osize = Array.length odata in
    let i = hash mod osize in
    odata.(i) <- Cons (key, hash, odata.(i));
    table.size <- table.size + 1;
    if table.size > osize lsl 1 then resize table

  let find_rec hash key table bucket =
    let rec aux = function
      | Empty ->
	add hash key table; key
      | Cons (k, h, rest) ->
	if hash == h && E.equal key k then k else aux rest
    in
    aux bucket

  let repr hash key table =
    let odata = table.data in
    let osize = Array.length odata in
    let i = hash mod osize in
    match odata.(i) with
      |	Empty -> add hash key table; key
      | Cons (k1, h1, rest1) ->
	if hash == h1 && E.equal key k1 then k1 else
	  match rest1 with
            | Empty -> add hash key table; key
	    | Cons (k2, h2, rest2) ->
              if hash == h2 && E.equal key k2 then k2 else
		match rest2 with
		  | Empty -> add hash key table; key
		  | Cons (k3, h3, rest3) ->
		    if hash == h2 && E.equal key k3 then k3
		    else find_rec hash key table rest3

end

module Combine = struct
    (* These are helper functions to combine the hash keys in a similar
       way as [Hashtbl.hash] does. The constants [alpha] and [beta] must
       be prime numbers. There were chosen empirically. Notice that the
       problem of hashing trees is hard and there are plenty of study on
       this topic. Therefore, there must be room for improvement here. *)
    let alpha = 65599
    let beta  = 7
    let combine x y     = x * alpha + y
    let combine3 x y z   = combine x (combine y z)
    let combine4 x y z t = combine x (combine3 y z t)
    let combinesmall x y = beta * x + y
end
