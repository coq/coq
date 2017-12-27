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
  end

module Make(Ord: OrderedType) =
  struct
    module EltSet = Set.Make(Ord)

    type elt = Ord.t

    (* (false, s) represents a set which is equal to the set s
       (true, s)  represents a set which is equal to the complement of set s *)
    type t = bool * EltSet.t

    let elements (b,s) = (b, EltSet.elements s)

    let empty = (false,EltSet.empty)
    let full = (true,EltSet.empty)

    (* assumes the set is infinite *)
    let is_empty (b,s) = not b && EltSet.is_empty s
    let is_full (b,s) = b && EltSet.is_empty s

    let mem x (b,s) =
      if b then not (EltSet.mem x s) else EltSet.mem x s

    let singleton x = (false,EltSet.singleton x)

    let add x (b,s) =
      if b then (b,EltSet.remove x s)
      else (b,EltSet.add x s)

    let remove x (b,s) =
      if b then (b,EltSet.add x s)
      else (b,EltSet.remove x s)

    let complement (b,s) = (not b, s)

    let union s1 s2 =
      match (s1,s2) with
          ((false,p1),(false,p2)) -> (false,EltSet.union p1 p2)
        | ((true,n1),(true,n2)) -> (true,EltSet.inter n1 n2)
        | ((false,p1),(true,n2)) -> (true,EltSet.diff n2 p1)
        | ((true,n1),(false,p2)) -> (true,EltSet.diff n1 p2)

    let inter s1 s2 =
      complement (union (complement s1) (complement s2))

    let diff s1 s2 = inter s1 (complement s2)

    (* assumes the set is infinite *)
    let subset s1 s2 =
      match (s1,s2) with
          ((false,p1),(false,p2)) -> EltSet.subset p1 p2
        | ((true,n1),(true,n2)) -> EltSet.subset n2 n1
        | ((false,p1),(true,n2)) -> EltSet.is_empty (EltSet.inter p1 n2)
        | ((true,_),(false,_)) -> false

    (* assumes the set is infinite *)
    let equal (b1,s1) (b2,s2) =
      b1=b2 && EltSet.equal s1 s2

  end
