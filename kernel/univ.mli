(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Qualified global universe level *)
module UGlobal :
sig

  type t

  val make : Names.DirPath.t -> string -> int -> t
  val repr : t -> Names.DirPath.t * string * int
  val equal : t -> t -> bool
  val hash : t -> int
  val compare : t -> t -> int
  val to_string : t -> string

end

(** Universes. *)
module Level :
sig

  type t
  (** Type of universe levels. A universe level is essentially a unique name
      that will be associated to constraints later on. A level can be local to a
      definition or global. *)

  val set : t
  (** The Set universe level. *)

  val is_set : t -> bool
  (** Is the universe Set? *)

  val compare : t -> t -> int
  (** Comparison function *)

  val equal : t -> t -> bool
  (** Equality function *)

  val hash : t -> int

  val hcons : t Hashcons.f

  val make : UGlobal.t -> t

  val raw_pr : t -> Pp.t
  (** Pretty-printing.
      When possible you should use name-aware printing. *)

  val pr : t -> Pp.t
  [@@deprecated "(8.18) Use [UnivNames.pr_with_global_universes] instead if possible, otherwise [raw_pr]."]

  val to_string : t -> string
  (** Debug printing *)

  val var : int -> t

  val var_index : t -> int option

  val name : t -> UGlobal.t option

  module Set :
    sig
      include CSig.USetS with type elt = t

      val pr : (elt -> Pp.t) -> t -> Pp.t
      (** Pretty-printing *)

      val hcons : t Hashcons.f
    end

  module Map :
  sig
    include CMap.UExtS with type key = t and module Set := Set

    val lunion : 'a t -> 'a t -> 'a t
    (** [lunion x y] favors the bindings in the first map. *)

    val diff : 'a t -> 'a t -> 'a t
    (** [diff x y] removes bindings from x that appear in y (whatever the value). *)

    val pr : (key -> Pp.t) -> ('a -> Pp.t) -> 'a t -> Pp.t
    (** Pretty-printing *)
  end
end

module LevelExpr :
sig
  type t = Level.t * int

  val equal : t -> t -> bool
  val compare : t -> t -> int

  val addn : t -> int -> t

  val pr : (Level.t -> Pp.t) -> t -> Pp.t

  val hash : t -> int

  module Set : CSet.ExtS with type elt  = t
  module Map : CMap.ExtS with type key = t and module Set := Set
end

module Universe :
sig

  type t
  (** Type of universes. A universe is defined as a set of level expressions.
      A level expression is built from levels and successors of level expressions, i.e.:
      le ::= l + n, n \in N.

      A universe is said atomic if it consists of a single level expression with
      no increment, and algebraic otherwise (think the least upper bound of a set of
      level expressions).
  *)

  val compare : t -> t -> int
  (** Comparison function *)

  val equal : t -> t -> bool
  (** Equality function on formal universes *)

  val hash : t -> int
  (** Hash function *)

  val hcons : t Hashcons.f

  val make : Level.t -> t
  (** Create a universe representing the given level. *)

  val maken : Level.t -> int -> t
  (** Composition of [make] and iterated [super]. *)

  val of_expr : LevelExpr.t -> t
  (** Create a singleton universe from a level expression *)

  val of_list : LevelExpr.t list -> t
  (** Create a universe representing the maximum of some non-empty level expressions. *)

  val pr : (Level.t -> Pp.t) -> t -> Pp.t
  (** Pretty-printing *)

  val raw_pr : t -> Pp.t

  val is_level : t -> bool
  (** Test if the universe is a level or an algebraic universe. *)

  val is_levels : t -> bool
  (** Test if the universe is a lub of levels or contains +n's. *)

  val level : t -> Level.t option
  (** Try to get a level out of a universe, returns [None] if it
      is an algebraic universe. *)

  val levels : ?init:Level.Set.t -> t -> Level.Set.t
  (** Get the levels inside the universe, forgetting about increments,
      and add them to [init] (default empty) *)

  val mem : Level.t -> t -> bool
  (** Does a level appear in a universe? *)

  val super : t -> t
  (** The universe strictly above *)

  val addn : t -> int -> t
  (** [addn u n] represents u + n (n is required to be >= 0) *)

  val sup   : t -> t -> t
  (** The l.u.b. of 2 universes *)

  val type0 : t
  (** image of Set in the universes hierarchy *)

  val type1 : t
  (** the universe of the type of Prop/Set *)

  val var : int -> t
  (** The universe variable n *)

  val is_type0 : t -> bool
  val is_typen : int -> t -> bool

  val sort : (Level.t * int) list -> t
  val exists : (Level.t * int -> bool) -> t -> bool
  val for_all : (Level.t * int -> bool) -> t -> bool

  val repr : t -> LevelExpr.t list
  val unrepr : LevelExpr.t list -> t

  val decompose_succ : t -> t option
  (** [decompose_succ u] returns [Some v] if [u = v + 1], otherwise [None] *)

  val make_subst_fn : t Level.Map.t -> (Level.t -> t)

  val subst_fn : (Level.t -> t) -> t -> t

  module Set : CSet.ExtS with type elt  = t
  module Map : CMap.ExtS with type key = t and module Set := Set

end

(** [univ_level_mem l u] Is l is mentioned in u ? *)

val univ_level_mem : Level.t -> Universe.t -> bool

(** [univ_level_rem u v min] removes [u] from [v], resulting in [min]
    if [v] was exactly [u]. *)

val univ_level_rem : Level.t -> Universe.t -> Universe.t -> Universe.t

(** {6 UnivConstraints. } *)

module UnivConstraint : sig
  type kind = Le | Eq
  val compare_kind : kind -> kind -> int
  val pr_kind : kind -> Pp.t
  type t = Universe.t * kind * Universe.t
end

module UnivConstraints : sig
  include CSet.ExtS with type elt = UnivConstraint.t

  val pr : (Level.t -> Pp.t) -> t -> Pp.t

  val hcons : t Hashcons.f
end

(** Enforcing UnivConstraints.t. *)
type 'a constraint_function = 'a -> 'a -> UnivConstraints.t -> UnivConstraints.t

val enforce : Universe.t -> UnivConstraint.kind -> Universe.t -> UnivConstraints.t -> UnivConstraints.t

val enforce_eq : Universe.t constraint_function
val enforce_leq : Universe.t constraint_function

val enforce_eq_level : Level.t constraint_function
val enforce_leq_level : Level.t constraint_function

(** Universe contexts (as sets) *)

(** A set of universes with universe UnivConstraints.t.
    We linearize the set to a list after typechecking.
    Beware, representation could change.
*)

module ContextSet :
sig
  type t = Level.Set.t * UnivConstraints.t

  val empty : t
  val is_empty : t -> bool

  val singleton : Level.t -> t
  val of_set : Level.Set.t -> t

  val equal : t -> t -> bool
  val union : t -> t -> t

  val append : t -> t -> t
  (** Variant of {!union} which is more efficient when the left argument is
      much smaller than the right one. *)

  val diff : t -> t -> t
  val add_universe : Level.t -> t -> t
  val add_constraints : UnivConstraints.t -> t -> t

  val constraints : t -> UnivConstraints.t
  val levels : t -> Level.Set.t

  val size : t -> int
  (** The number of universes in the context *)

  val hcons : t Hashcons.f

  val pr : (Level.t -> Pp.t) -> t -> Pp.t


end
