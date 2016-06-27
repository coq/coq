(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Hash consing of datastructures *)

(* The generic hash-consing functions (does not use Obj) *)

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

(* For a recursive type T, we write the module of sig Comp with u equals
 * to (T -> T) * u0
 * The first component will be used to hash-cons the recursive subterms
 * The second one to hashcons the other sub-structures.
 * We just have to take the fixpoint of h
 *)
let recursive_hcons h f u =
  let loop = ref (fun _ -> assert false) in
  let self x = !loop x in
  let table = h (self, u) in
  let hrec x = f table x in
  let () = loop := hrec in
  hrec

(* Basic hashcons modules for string and obj. Integers do not need be
   hashconsed.  *)

module type HashedType = sig type t val hash : t -> int end

(* list *)
module Hlist (D:HashedType) =
  Make(
    struct
      type t = D.t list
      type u = (t -> t) * (D.t -> D.t)
      let hashcons (hrec,hdata) = function
        | x :: l -> hdata x :: hrec l
        | l -> l
      let eq l1 l2 =
        l1 == l2 ||
          match l1, l2 with
          | [], [] -> true
          | x1::l1, x2::l2 -> x1==x2 && l1==l2
          | _ -> false
      let rec hash accu = function
      | [] -> accu
      | x :: l ->
        let accu = Hashset.Combine.combine (D.hash x) accu in
        hash accu l
      let hash l = hash 0 l
    end)

(* string *)
module Hstring = Make(
  struct
    type t = string
    type u = unit
    let hashcons () s =(* incr accesstr;*) s
    external eq : string -> string -> bool = "caml_string_equal" "noalloc"
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

(* Obj.t *)
exception NotEq

(* From CAMLLIB/caml/mlvalues.h *)
let no_scan_tag = 251
let tuple_p obj = Obj.is_block obj && (Obj.tag obj < no_scan_tag)

let comp_obj o1 o2 =
  if tuple_p o1 && tuple_p o2 then
    let n1 = Obj.size o1 and n2 = Obj.size o2 in
      if n1=n2 then
        try
          for i = 0 to pred n1 do
            if not (Obj.field o1 i == Obj.field o2 i) then raise NotEq
          done; true
        with NotEq -> false
      else false
  else o1=o2

let hash_obj hrec o =
  begin
    if tuple_p o then
      let n = Obj.size o in
        for i = 0 to pred n do
          Obj.set_field o i (hrec (Obj.field o i))
        done
  end;
  o

module Hobj = Make(
  struct
    type t = Obj.t
    type u = (Obj.t -> Obj.t) * unit
    let hashcons (hrec,_) = hash_obj hrec
    let eq = comp_obj
    let hash = Hashtbl.hash
  end)
