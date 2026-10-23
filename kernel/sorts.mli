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

module QGlobal :
sig

  type t

  val make : Names.DirPath.t -> int -> t
  val repr : t -> Names.DirPath.t * int
  val equal : t -> t -> bool
  val hash : t -> int
  val compare : t -> t -> int

  val to_string : t -> string

  module Set : sig
    include CSig.SetS with type elt = t
    val pr : (elt -> Pp.t) -> t -> Pp.t
  end

end

module QVar :
sig
  type t

  val var_index : t -> int option

  val make_var : int -> t
  val make_secvar : int -> t
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
    | Secvar of int
    | Unif of string * int

  val repr : t -> repr
  val of_repr : repr -> t

  val is_secvar : t -> bool
  val is_unif : t -> bool

  module Set : sig
    include CSig.SetS with type elt = t
    val pr : (elt -> Pp.t) -> t -> Pp.t
  end

  module Map : CMap.ExtS with type key = t and module Set := Set
end

module Quality : sig
  type constant = QProp | QSProp | QType
  type t = QVar of QVar.t | QConstant of constant | QGlobal of QGlobal.t

  module Constants : sig
    val equal : constant -> constant -> bool
    val compare : constant -> constant -> int
    val pr : constant -> Pp.t
  end

  val qprop : t
  val qsprop : t
  val qtype : t
  val is_qprop : t -> bool
  val is_qsprop : t -> bool
  val is_qtype : t -> bool
  val is_qvar : t -> bool
  val is_qconst : t -> bool
  val is_qglobal : t -> bool
  val is_impredicative : t -> bool

  val var : int -> t
  (** [var i] is [QVar (QVar.make_var i)] *)

  val global : QGlobal.t -> t
  (** [global i] is [QVar (QVar.make_global i)] *)

  val var_index : t -> int option

  val equal : t -> t -> bool

  val compare : t -> t -> int

  type printer = {
    prvar : QVar.t -> Pp.t;
    prglobal : QGlobal.t -> Pp.t;
  }

  val pr : printer -> t -> Pp.t

  val raw_printer : printer

  val raw_pr : t -> Pp.t

  val all_constants : t list

  val hash : t -> int

  val hcons : t Hashcons.f

  (* XXX Inconsistent naming: this one should be subst_fn *)
  val subst : (QVar.t -> t) -> t -> t

  val subst_fn : t QVar.Map.t -> QVar.t -> t

  module Set : sig
    include CSig.SetS with type elt = t

    val of_qvars : QVar.Set.t -> t

    val of_qglobals : QGlobal.Set.t -> t
  end

  module Map : CMap.ExtS with type key = t and module Set := Set

  type 'q pattern =
    PQVar of 'q | PQConstant of constant | PQGlobal of QGlobal.t

  val pattern_match : int option pattern -> t -> ('t, t, 'u) Partial_subst.t -> ('t, t, 'u) Partial_subst.t option
end

module ElimConstraint : sig
  type kind = ElimTo

  val pr_kind : kind -> Pp.t

  type t = Quality.t * kind * Quality.t

  val equal : t -> t -> bool

  val compare : t -> t -> int

  val pr : Quality.printer -> t -> Pp.t

  val raw_pr : t -> Pp.t
end

module ElimConstraints : sig include CSet.ExtS with type elt = ElimConstraint.t
  val pr : Quality.printer -> t -> Pp.t

  val hcons : t Hashcons.f
end

module QContextSet :
sig
  type t = QVar.Set.t * ElimConstraints.t
  val empty : t
  val is_empty : t -> bool
  val union : t -> t -> t
end

type t = private
  | SProp
  | Prop
  | Set
  | Type of Univ.Universe.t
  | GSort of QGlobal.t * Univ.Universe.t
  | VSort of QVar.t * Univ.Universe.t

val sprop : t
val set  : t
val prop : t
val type1  : t
val gsort : QGlobal.t -> Univ.Universe.t -> t
val vsort : QVar.t -> Univ.Universe.t -> t
val make : Quality.t -> Univ.Universe.t -> t

val equal : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int

val is_sprop : t -> bool
val is_set : t -> bool
val is_prop : t -> bool
val quality : t -> Quality.t

val hcons : t Hashcons.f

val sort_of_univ : Univ.Universe.t -> t
val univ_of_sort : t -> Univ.Universe.t

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

val is_relevant : relevance -> bool

val debug_print : t -> Pp.t

type printer = {
  prq : Quality.printer;
  pru : Univ.Level.t -> Pp.t;
}

val pr : printer -> t -> Pp.t

val raw_printer : printer

val raw_pr : t -> Pp.t

type ('q, 'u) pattern =
  | PSProp | PSSProp | PSSet | PSType of 'u | PSGlobal of QGlobal.t * 'u | PSQSort of 'q * 'u

val make_pattern : 'q Quality.pattern -> 'u -> ('q, 'u) pattern

val pattern_match : (int option, int option) pattern -> t -> ('t, Quality.t, Univ.Level.t) Partial_subst.t -> ('t, Quality.t, Univ.Level.t) Partial_subst.t option
