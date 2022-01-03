(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Hash consing of datastructures *)

(* [t] is the type of object to hash-cons
 * [u] is the type of hash-cons functions for the sub-structures
 *   of objects of type t (u usually has the form (t1->t1)*(t2->t2)*...).
 * [hashcons u x] is a function that hash-cons the sub-structures of x using
 *   the hash-consing functions u provides.
 * [eq] is a comparison function. It is allowed to use physical equality
 *   on the sub-terms hash-consed by the hashcons function.
 * [hash] is the hash function given to the Hashtbl.Make function
 *
 * Note that this module type coerces to the argument of Hashtbl.Make.
 *)

module type HashconsedType =
  sig
    type t
    type u
    val hashcons :  u -> t -> t
    val eq : t -> t -> bool
    val hash : t -> int
  end

(** The output is a function [generate] such that [generate args] creates a
    hash-table of the hash-consed objects, together with [hcons], a function
    taking a table and an object, and hashcons it. For simplicity of use, we use
    the wrapper functions defined below. *)

module type S =
  sig
    type t
    type u
    type table
    val generate : u -> table
    val hcons : table -> t -> t
    val stats : table -> Hashset.statistics
  end

module Make (X : HashconsedType) : (S with type t = X.t and type u = X.u) =
  struct
    type t = X.t
    type u = X.u

    (* We create the type of hashtables for t, with our comparison fun.
     * An invariant is that the table never contains two entries equals
     * w.r.t (=), although the equality on keys is X.eq. This is
     * granted since we hcons the subterms before looking up in the table.
     *)
    module Htbl = Hashset.Make(X)

    type table = (Htbl.t * u)

    let generate u =
      let tab = Htbl.create 97 in
      (tab, u)

    let hcons (tab, u) x =
      let y = X.hashcons u x in
      Htbl.repr (X.hash y) y tab

    let stats (tab, _) = Htbl.stats tab

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

module type HashedType = sig type t val hash : t -> int end

(* list *)
module Hlist (D:HashedType) =
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
    type u = (D.t -> D.t)

    module Htbl = Hashset.Make(X)

    type table = (Htbl.t * u)

    let generate u =
      let tab = Htbl.create 97 in
      (tab, u)

    let rec hcons (tab, hdata as data) l =
      let h, l = match l with
      | [] -> 0, []
      | x :: l ->
        let h, l = hcons data l in
        let h = Hashset.Combine.combine (D.hash x) h in
        h, hdata x :: l
      in
      h, Htbl.repr h l tab

    let hcons data l = snd (hcons data l)

    let stats (tab, _) = Htbl.stats tab

  end

(* string *)
module Hstring = Make(
  struct
    type t = string
    type u = unit
    let hashcons () s =(* incr accesstr;*) s

    let eq = String.equal

    (** Copy from CString *)
    let rec hash len s i accu =
      if i = len then accu
      else
        let c = Char.code (String.unsafe_get s i) in
        hash len s (succ i) (accu * 19 + c)

    let hash s =
      let len = String.length s in
      hash len s 0 0
  end)
