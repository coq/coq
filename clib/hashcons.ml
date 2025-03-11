(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Hash consing of datastructures *)

type 'a f = 'a -> int * 'a

(* [t] is the type of object to hash-cons
 * [hashcons x] is a function that hash-cons the sub-structures of x
 * [eq] is a comparison function. It is allowed to use physical equality
 *   on the sub-terms hash-consed by the hashcons function.
 *)

module type HashconsedType =
  sig
    type t
    val hashcons : t f
    val eq : t -> t -> bool
  end

module type HashconsedRecType = sig
  type t

  val hashcons : t f -> t f

  val eq : t -> t -> bool

end

(** The output is a function [generate] such that [generate args] creates a
    hash-table of the hash-consed objects, together with [hcons], a function
    taking a table and an object, and hashcons it. For simplicity of use, we use
    the wrapper functions defined below. *)

module type S =
  sig
    type t
    type table
    val generate : unit -> table
    val hcons : table -> t f
    val stats : table -> Hashset.statistics
  end

module Make (X : HashconsedType) : (S with type t = X.t) =
  struct
    type t = X.t

    (* We create the type of hashtables for t, with our comparison fun.
     * An invariant is that the table never contains two entries equals
     * w.r.t (=), although the equality on keys is X.eq. This is
     * granted since we hcons the subterms before looking up in the table.
     *)
    module Htbl = Hashset.Make(X)

    type table = Htbl.t

    let generate () =
      let tab = Htbl.create 97 in
      tab

    let hcons tab x =
      let h, y = X.hashcons x in
      h, Htbl.repr h y tab

    let stats = Htbl.stats

  end

module MakeRec (X : HashconsedRecType) : (S with type t = X.t) =
struct
  type t = X.t

  module Htbl = Hashset.Make(X)

  type table = Htbl.t

  let generate () =
    let tab = Htbl.create 97 in
    tab

  let rec hcons tab x =
    let h, y = X.hashcons (hcons tab) x in
    h, Htbl.repr h y tab

  let stats = Htbl.stats

end

(* A few useful wrappers:
 * takes as argument the function [generate] above and build a function of type
 * u -> t -> t that creates a fresh table each time it is applied to the
 * sub-hcons functions. *)

(* For non-recursive types it is quite easy. *)
let simple_hcons h f u =
  let table = h u in
  fun x -> f table x

(* Basic hashcons modules for string and obj. Integers do not need be
   hashconsed.  *)

module type HashedType = sig
  type t
  val hcons : t f
end

(* list *)
module Hlist (D:HashedType) : S with type t = D.t list =
  struct
    module X =
    struct
      type t = D.t list
      let eq l1 l2 =
        l1 == l2 ||
          match l1, l2 with
          | [], [] -> true
          | x1::l1, x2::l2 -> x1==x2 && l1==l2
          | _ -> false
    end

    type t = X.t

    module Htbl = Hashset.Make(X)

    type table = Htbl.t

    let generate () =
      let tab = Htbl.create 97 in
      tab

    let rec hcons tab l =
      let h, l = match l with
      | [] -> 0, []
      | x :: l ->
        let hx, x = D.hcons x in
        let h, l = hcons tab l in
        let h = Hashset.Combine.combine hx h in
        h, x :: l
      in
      h, Htbl.repr h l tab

    let stats = Htbl.stats

  end

let hashcons_array hcons a =
  CArray.Smart.fold_left_map (fun acc x ->
      let hx, x = hcons x in
      Hashset.Combine.combine acc hx, x)
    0
    a
