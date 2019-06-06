(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** {6 The sorts of CCI. } *)

type family = InSProp | InProp | InSet | InType

type t = private
  | SProp
  | Prop
  | Set
  | Type of Univ.Universe.t

val sprop : t
val set  : t
val prop : t
val type1  : t

val equal : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int

val is_sprop : t -> bool
val is_set : t -> bool
val is_prop : t -> bool
val is_small : t -> bool
val family : t -> family

val hcons : t -> t

val family_compare : family -> family -> int
val family_equal : family -> family -> bool
val family_leq : family -> family -> bool

val univ_of_sort : t -> Univ.Universe.t
val sort_of_univ : Univ.Universe.t -> t

val super : t -> t

(** On binders: is this variable proof relevant *)
type relevance = Relevant | Irrelevant

val relevance_hash : relevance -> int

val relevance_equal : relevance -> relevance -> bool

val relevance_of_sort : t -> relevance
val relevance_of_sort_family : family -> relevance

val debug_print : t -> Pp.t

val pr_sort_family : family -> Pp.t
