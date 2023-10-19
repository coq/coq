(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License.         *)
(*                                                                     *)
(************************************************************************)

module type OrderedType =
  sig
    type t
    val compare: t -> t -> int
  end

module type S =
  sig
    type elt
    type t
    val empty: t
    val full: t
    val is_empty: t -> bool
    val is_full: t -> bool
    val mem: elt -> t -> bool
    val singleton: elt -> t
    val add: elt -> t -> t
    val remove: elt -> t -> t
    val union: t -> t -> t
    val inter: t -> t -> t
    val diff: t -> t -> t
    val complement: t -> t
    val equal: t -> t -> bool
    val subset: t -> t -> bool
    val elements: t -> bool * elt list
    val is_finite : t -> bool
  end

module Make(Ord: OrderedType) =
  struct
    module EltSet = Set.Make(Ord)

    type elt = Ord.t

    type t =
      | Just of EltSet.t
      | AllExcept of EltSet.t

    let is_finite = function
      | Just _ -> true
      | AllExcept _ -> false

    let elements = function
      | Just s -> (false, EltSet.elements s)
      | AllExcept s -> (true, EltSet.elements s)

    let empty = Just EltSet.empty
    let full = AllExcept EltSet.empty

    (* assumes the set is infinite *)
    let is_empty = function
      | Just s -> EltSet.is_empty s
      | AllExcept _ -> false
    let is_full = function
      | Just _ -> false
      | AllExcept s -> EltSet.is_empty s

    let mem x = function
      | Just s -> EltSet.mem x s
      | AllExcept s -> not (EltSet.mem x s)

    let singleton x = Just (EltSet.singleton x)

    let add x = function
      | Just s -> Just (EltSet.add x s)
      | AllExcept s -> AllExcept (EltSet.remove x s)

    let remove x = function
      | Just s -> Just (EltSet.remove x s)
      | AllExcept s -> AllExcept (EltSet.add x s)

    let complement = function
      | Just s -> AllExcept s
      | AllExcept s -> Just s

    let union s1 s2 =
      match (s1,s2) with
      | Just p1, Just p2 -> Just (EltSet.union p1 p2)
      | AllExcept n1, AllExcept n2 -> AllExcept (EltSet.inter n1 n2)
      | Just p, AllExcept n | AllExcept n, Just p -> AllExcept (EltSet.diff n p)

    let inter s1 s2 =
      complement (union (complement s1) (complement s2))

    let diff s1 s2 = inter s1 (complement s2)

    (* assumes the set is infinite *)
    let subset s1 s2 =
      match (s1,s2) with
      | Just p1, Just p2 -> EltSet.subset p1 p2
      | AllExcept n1, AllExcept n2 -> EltSet.subset n2 n1
      | Just p1, AllExcept n2 -> EltSet.is_empty (EltSet.inter p1 n2)
      | AllExcept _, Just _ -> false

    (* assumes the set is infinite *)
    let equal x y = match x,y with
      | Just s1, Just s2 | AllExcept s1, AllExcept s2 -> EltSet.equal s1 s2
      | Just _, AllExcept _ | AllExcept _, Just _ -> false

  end
