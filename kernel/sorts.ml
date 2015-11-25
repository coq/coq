(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Univ

type family = InProp | InSet | InType

type t =
  | Prop                   (** [Prop] *)
  | Set                    (** [Set] *)
  | Type of Univ.universe  (** [Type] *)

let prop = Prop
let set = Set
let type1 = Type type1_univ

let univ_of_sort = function
  | Type u -> u
  | Set -> Universe.type0
  | Prop -> Universe.type0m

let sort_of_univ u =
  if is_type0m_univ u then prop
  else if is_type0_univ u then set
  else Type u

let compare s1 s2 =
  if s1 == s2 then 0 else
    match s1, s2 with
    | Set, Prop -> -1
    | Set, Type _ -> -1
    | Prop, Type _ -> -1
    | Set, Set -> 0
    | Prop, Prop -> 0
    | Type _, Prop -> 1
    | Type _, Set -> 1
    | Prop, Set -> 1
    | Type u1, Type u2 -> Universe.compare u1 u2

let equal s1 s2 = Int.equal (compare s1 s2) 0

let is_prop = function
  | Prop -> true
  | Set -> false
  | Type u -> Universe.equal Universe.type0m u

let is_set = function
  | Prop -> false
  | Set -> true
  | Type u -> Universe.equal Universe.type0 u

let is_small = function
  | Prop | Set -> true
  | Type u -> is_small_univ u

let family = function
  | Prop -> InProp
  | Set -> InSet
  | Type u ->
      if is_type0m_univ u then InProp
      else if is_type0_univ u then InSet
      else InType

let family_equal = (==)

open Hashset.Combine

let hash = function
  | Prop -> combinesmall 1 1
  | Set -> combinesmall 1 0
  | Type u ->
      let h = Univ.Universe.hash u in
      combinesmall 2 h

module List = struct
  let mem = List.memq
  let intersect l l' = CList.intersect family_equal l l'
end

module Hsorts =
  Hashcons.Make(
    struct
      type _t = t
      type t = _t
      type u = universe -> universe

      let hashcons huniv = function
        | Type u as c -> 
	  let u' = huniv u in 
	    if u' == u then c else Type u'
        | s -> s
      let equal s1 s2 = match (s1,s2) with
        | Prop, Prop -> true
        | Set, Set -> true
        | Type u1, Type u2 -> u1 == u2
        |_ -> false

      let hash = hash
    end)

let hcons = Hashcons.simple_hcons Hsorts.generate Hsorts.hcons hcons_univ
