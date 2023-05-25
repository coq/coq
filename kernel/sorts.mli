(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** {6 The sorts of CCI. } *)

type family = InSProp | InProp | InSet | InType | InQSort

val all_families : family list

module QVar :
sig
  type t
  val make : int -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pr : t -> Pp.t
  val to_string : t -> string
end

type t = private
  | SProp
  | Prop
  | Set
  | Type of Univ.Universe.t
  | QSort of QVar.t * Univ.Universe.t

val sprop : t
val set  : t
val prop : t
val type1  : t
val qsort : QVar.t -> Univ.Universe.t -> t

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

val sort_of_univ : Univ.Universe.t -> t

val levels : t -> Univ.Level.Set.t

val super : t -> t

val subst_instance_sort : Univ.Instance.t -> t -> t

(** On binders: is this variable proof relevant *)
type relevance = Relevant | Irrelevant | RelevanceVar of QVar.t

val relevance_hash : relevance -> int

val relevance_equal : relevance -> relevance -> bool

val relevance_of_sort : t -> relevance
val relevance_of_sort_family : family -> relevance

val debug_print : t -> Pp.t

val pr_sort_family : family -> Pp.t
