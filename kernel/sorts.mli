(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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

  val var_index : t -> int option

  val make_var : int -> t
  val make_unif : string -> int -> t

  val equal : t -> t -> bool
  val compare : t -> t -> int

  val hash : t -> int

  val raw_pr : t -> Pp.t
  (** Using this is incorrect when names are available, typically from an evar map. *)

  val to_string : t -> string
  (** Debug printing *)

  type repr =
    | Var of int
    | Unif of string * int

  val repr : t -> repr
  val of_repr : repr -> t

  module Set : CSig.SetS with type elt = t

  module Map : CMap.ExtS with type key = t and module Set := Set
end

module Quality : sig
  type constant = QProp | QSProp | QType
  type t = QVar of QVar.t | QConstant of constant

  module Constants : sig
    val equal : constant -> constant -> bool
    val compare : constant -> constant -> int
    val pr : constant -> Pp.t
  end

  val qprop : t
  val qsprop : t
  val qtype : t

  val var : int -> t
  (** [var i] is [QVar (QVar.make_var i)] *)

  val var_index : t -> int option

  val equal : t -> t -> bool

  val compare : t -> t -> int

  val pr : (QVar.t -> Pp.t) -> t -> Pp.t

  val raw_pr : t -> Pp.t

  val hash : t -> int

  val hcons : t -> t

  (* XXX Inconsistent naming: this one should be subst_fn *)
  val subst : (QVar.t -> t) -> t -> t

  val subst_fn : t QVar.Map.t -> QVar.t -> t

  module Set : CSig.SetS with type elt = t

  module Map : CMap.ExtS with type key = t and module Set := Set

  type pattern =
    PQVar of int option | PQConstant of constant

  val pattern_match : pattern -> t -> ('t, t, 'u) Partial_subst.t -> ('t, t, 'u) Partial_subst.t option
end

module QConstraint : sig
  type kind = Equal | Leq

  val pr_kind : kind -> Pp.t

  type t = Quality.t * kind * Quality.t

  val equal : t -> t -> bool

  val compare : t -> t -> int

  val trivial : t -> bool

  val pr : (QVar.t -> Pp.t) -> t -> Pp.t

  val raw_pr : t -> Pp.t
end

module QConstraints : sig include CSig.SetS with type elt = QConstraint.t

  val trivial : t -> bool

  val pr : (QVar.t -> Pp.t) -> t -> Pp.t
end

val enforce_eq_quality : Quality.t -> Quality.t -> QConstraints.t -> QConstraints.t

val enforce_leq_quality : Quality.t -> Quality.t -> QConstraints.t -> QConstraints.t

module QUConstraints : sig

  type t = QConstraints.t * Univ.Constraints.t

  val union : t -> t -> t

  val empty : t
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
val make : Quality.t -> Univ.Universe.t -> t

val equal : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int

val is_sprop : t -> bool
val is_set : t -> bool
val is_prop : t -> bool
val is_small : t -> bool
val family : t -> family
val quality : t -> Quality.t

val hcons : t -> t

val family_compare : family -> family -> int
val family_equal : family -> family -> bool
val family_leq : family -> family -> bool

val sort_of_univ : Univ.Universe.t -> t

val levels : t -> Univ.Level.Set.t

val super : t -> t

val subst_fn : (QVar.t -> Quality.t) * (Univ.Universe.t -> Univ.Universe.t)
  -> t -> t

(** On binders: is this variable proof relevant *)
(* TODO put in submodule or new file *)
type relevance = Relevant | Irrelevant | RelevanceVar of QVar.t

val relevance_hash : relevance -> int

val relevance_equal : relevance -> relevance -> bool

val relevance_subst_fn : (QVar.t -> Quality.t) -> relevance -> relevance

val relevance_of_sort : t -> relevance
val relevance_of_sort_family : family -> relevance

val debug_print : t -> Pp.t

val pr_sort_family : family -> Pp.t

type pattern =
  | PSProp | PSSProp | PSSet | PSType of int option | PSQSort of int option * int option

val pattern_match : pattern -> t -> ('t, Quality.t, Univ.Level.t) Partial_subst.t -> ('t, Quality.t, Univ.Level.t) Partial_subst.t option
