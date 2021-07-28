(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Universes. *)
module Level :
sig

  module UGlobal : sig
    type t

    val make : Names.DirPath.t -> string -> int -> t
    val repr : t -> Names.DirPath.t * string * int
    val equal : t -> t -> bool
    val hash : t -> int
    val compare : t -> t -> int

  end
  (** Qualified global universe level *)

  type t
  (** Type of universe levels. A universe level is essentially a unique name
      that will be associated to constraints later on. A level can be local to a
      definition or global. *)

  val set : t
  val prop : t
  val sprop : t
  (** The set and prop universe levels. *)

  val is_small : t -> bool
  (** Is the universe set or prop? *)

  val is_sprop : t -> bool
  val is_prop : t -> bool
  val is_set : t -> bool
  (** Is it specifically Prop or Set *)

  val compare : t -> t -> int
  (** Comparison function *)

  val equal : t -> t -> bool
  (** Equality function *)

  val hash : t -> int

  val make : UGlobal.t -> t

  val pr : t -> Pp.t
  (** Pretty-printing *)

  val to_string : t -> string
  (** Debug printing *)

  val var : int -> t

  val var_index : t -> int option

  val name : t -> UGlobal.t option

  module Set :
    sig
      include CSig.SetS with type elt = t

      val pr : (elt -> Pp.t) -> t -> Pp.t
      (** Pretty-printing *)
    end

  module Map :
  sig
    include CMap.ExtS with type key = t and module Set := Set

    val lunion : 'a t -> 'a t -> 'a t
    (** [lunion x y] favors the bindings in the first map. *)

    val diff : 'a t -> 'a t -> 'a t
    (** [diff x y] removes bindings from x that appear in y (whatever the value). *)

    val subst_union : 'a option t -> 'a option t -> 'a option t
    (** [subst_union x y] favors the bindings of the first map that are [Some],
        otherwise takes y's bindings. *)

    val pr : ('a -> Pp.t) -> 'a t -> Pp.t
    (** Pretty-printing *)
  end

end

module LSet :
sig
  include CSig.SetS with type elt = Level.t and type t = Level.Set.t
  val pr : (Level.t -> Pp.t) -> t -> Pp.t
end [@@ocaml.deprecated "Use Univ.Level.Set"]

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

  val make : Level.t -> t
  (** Create a universe representing the given level. *)

  val pr : t -> Pp.t
  (** Pretty-printing *)

  val pr_with : (Level.t -> Pp.t) -> t -> Pp.t

  val is_level : t -> bool
  (** Test if the universe is a level or an algebraic universe. *)

  val is_levels : t -> bool
  (** Test if the universe is a lub of levels or contains +n's. *)

  val level : t -> Level.t option
  (** Try to get a level out of a universe, returns [None] if it
      is an algebraic universe. *)

  val levels : t -> Level.Set.t
  (** Get the levels inside the universe, forgetting about increments *)

  val super : t -> t
  (** The universe strictly above *)

  val sup   : t -> t -> t
  (** The l.u.b. of 2 universes *)

  val sprop : t

  val type0m : t
  (** image of Prop in the universes hierarchy *)

  val type0 : t
  (** image of Set in the universes hierarchy *)

  val type1 : t
  (** the universe of the type of Prop/Set *)

  val is_sprop : t -> bool
  val is_type0m : t -> bool
  val is_type0 : t -> bool

  val exists : (Level.t * int -> bool) -> t -> bool
  val for_all : (Level.t * int -> bool) -> t -> bool
  val repr : t -> (Level.t * int) list

  module Set : CSet.S with type elt  = t
  module Map : CMap.ExtS with type key = t and module Set := Set

end

(** Alias name. *)

val pr_uni : Universe.t -> Pp.t

(** The universes hierarchy: Type 0- = Prop <= Type 0 = Set <= Type 1 <= ...
   Typing of universes: Type 0-, Type 0 : Type 1; Type i : Type (i+1) if i>0 *)
val type0m_univ : Universe.t
val type0_univ : Universe.t
val type1_univ : Universe.t

val is_type0_univ : Universe.t -> bool
val is_type0m_univ : Universe.t -> bool
val is_univ_variable : Universe.t -> bool
val is_small_univ : Universe.t -> bool

val sup : Universe.t -> Universe.t -> Universe.t
val super : Universe.t -> Universe.t

val universe_level : Universe.t -> Level.t option

(** [univ_level_mem l u] Is l is mentioned in u ? *)

val univ_level_mem : Level.t -> Universe.t -> bool

(** [univ_level_rem u v min] removes [u] from [v], resulting in [min]
    if [v] was exactly [u]. *)

val univ_level_rem : Level.t -> Universe.t -> Universe.t -> Universe.t

(** {6 Constraints. } *)

type constraint_type = AcyclicGraph.constraint_type = Lt | Le | Eq
type univ_constraint = Level.t * constraint_type * Level.t

module Constraints : sig
 include Set.S with type elt = univ_constraint
end

module Constraint : sig
 include Set.S with type elt = univ_constraint and type t = Constraints.t
end [@@ocaml.deprecated "Use Univ.Constraints"]

val empty_constraint : Constraints.t
val union_constraint : Constraints.t -> Constraints.t -> Constraints.t
val eq_constraint : Constraints.t -> Constraints.t -> bool

(** A value with universe Constraints.t. *)
type 'a constrained = 'a * Constraints.t

(** Constrained *)
val constraints_of : 'a constrained -> Constraints.t

(** Enforcing Constraints.t. *)
type 'a constraint_function = 'a -> 'a -> Constraints.t -> Constraints.t

val enforce_eq : Universe.t constraint_function
val enforce_leq : Universe.t constraint_function
val enforce_eq_level : Level.t constraint_function
val enforce_leq_level : Level.t constraint_function

(** Type explanation is used to decorate error messages to provide
  useful explanation why a given constraint is rejected. It is composed
  of a path of universes and relation kinds [(r1,u1);..;(rn,un)] means
   .. <(r1) u1 <(r2) ... <(rn) un (where <(ri) is the relation symbol
  denoted by ri, currently only < and <=). The lowest end of the chain
  is supposed known (see UniverseInconsistency exn). The upper end may
  differ from the second univ of UniverseInconsistency because all
  universes in the path are canonical. Note that each step does not
  necessarily correspond to an actual constraint, but reflect how the
  system stores the graph and may result from combination of several
  Constraints.t...
*)
type explanation = (constraint_type * Level.t) list
type univ_inconsistency = constraint_type * Universe.t * Universe.t * explanation Lazy.t option

exception UniverseInconsistency of univ_inconsistency

(** {6 Support for universe polymorphism } *)

module LMap :
sig
  include CMap.ExtS with type key = Level.t and type 'a t = 'a Level.Map.t and module Set := Level.Set
  val lunion : 'a t -> 'a t -> 'a t
  val diff : 'a t -> 'a t -> 'a t
  val subst_union : 'a option t -> 'a option t -> 'a option t
  val pr : ('a -> Pp.t) -> 'a t -> Pp.t
end [@@ocaml.deprecated "Use Univ.Level.Map"]

type 'a universe_map = 'a Level.Map.t

(** {6 Substitution} *)

type universe_subst_fn = Level.t -> Universe.t
type universe_level_subst_fn = Level.t -> Level.t

(** A full substitution, might involve algebraic universes *)
type universe_subst = Universe.t universe_map
type universe_level_subst = Level.t universe_map

module Variance :
sig
  (** A universe position in the instance given to a cumulative
     inductive can be the following. Note there is no Contravariant
     case because [forall x : A, B <= forall x : A', B'] requires [A =
     A'] as opposed to [A' <= A]. *)
  type t = Irrelevant | Covariant | Invariant

  (** [check_subtype x y] holds if variance [y] is also an instance of [x] *)
  val check_subtype : t -> t -> bool

  val sup : t -> t -> t

  val pr : t -> Pp.t

  val equal : t -> t -> bool

end

(** {6 Universe instances} *)

module Instance :
sig
  type t
  (** A universe instance represents a vector of argument universes
      to a polymorphic definition (constant, inductive or constructor). *)

  val empty : t
  val is_empty : t -> bool

  val of_array : Level.t array -> t
  val to_array : t -> Level.t array

  val append : t -> t -> t
  (** To concatenate two instances, used for discharge *)

  val equal : t -> t -> bool
  (** Equality *)

  val length : t -> int
  (** Instance length *)

  val hcons : t -> t
  (** Hash-consing. *)

  val hash : t -> int
  (** Hash value *)

  val share : t -> t * int
  (** Simultaneous hash-consing and hash-value computation *)

  val subst_fn : universe_level_subst_fn -> t -> t
  (** Substitution by a level-to-level function. *)

  val pr : (Level.t -> Pp.t) -> ?variance:Variance.t array -> t -> Pp.t
  (** Pretty-printing, no comments *)

  val levels : t -> Level.Set.t
  (** The set of levels in the instance *)

end

val enforce_eq_instances : Instance.t constraint_function

val enforce_eq_variance_instances : Variance.t array -> Instance.t constraint_function
val enforce_leq_variance_instances : Variance.t array -> Instance.t constraint_function

type 'a puniverses = 'a * Instance.t
val out_punivs : 'a puniverses -> 'a
val in_punivs : 'a -> 'a puniverses

val eq_puniverses : ('a -> 'a -> bool) -> 'a puniverses -> 'a puniverses -> bool

(** A vector of universe levels with universe Constraints.t,
    representing local universe variables and associated Constraints.t;
    the names are user-facing names for printing *)

module UContext :
sig
  type t

  val make : Names.Name.t array -> Instance.t constrained -> t

  val empty : t
  val is_empty : t -> bool

  val instance : t -> Instance.t
  val constraints : t -> Constraints.t

  val union : t -> t -> t
  (** Keeps the order of the instances *)

  val size : t -> int
  (** The number of universes in the context *)

  val names : t -> Names.Name.t array
  (** Return the user names of the universes *)

  val refine_names : Names.Name.t array -> t -> t
  (** Use names to name the possibly yet unnamed universes *)

end

module AbstractContext :
sig
  type t
  (** An abstract context serves to quantify over a graph of universes
      represented using de Bruijn indices, as in:
      u0, ..., u(n-1), Var i < Var j, .., Var k <= Var l |- term(Var 0 .. Var (n-1))
      \-------------/  \-------------------------------/    \---------------------/
      names for        constraints expressed on de Bruijn   judgement in abstract
      printing         representation of the n univ vars    context expected to
                                                            use de Bruijn indices
  *)

  val make : Names.Name.t array -> Constraints.t -> t
  (** Build an abstract context. Constraints may be between universe
     variables. *)

  val repr : t -> UContext.t
  (** [repr ctx] is [(Var(0), ... Var(n-1) |= cstr] where [n] is the length of
      the context and [cstr] the abstracted Constraints.t. *)

  val empty : t
  val is_empty : t -> bool

  val size : t -> int

  val union : t -> t -> t
  (** The constraints are expected to be relative to the concatenated set of universes *)

  val instantiate : Instance.t -> t -> Constraints.t
  (** Generate the set of instantiated Constraints.t **)

  val names : t -> Names.Name.t array
  (** Return the names of the bound universe variables *)

end

module AUContext :
sig
  type t = AbstractContext.t
  val make : Names.Name.t array -> Constraints.t -> t
  val repr : t -> UContext.t
  val empty : t
  val is_empty : t -> bool
  val size : t -> int
  val union : t -> t -> t
  val instantiate : Instance.t -> t -> Constraints.t
  val names : t -> Names.Name.t array
end [@@ocaml.deprecated "Use Univ.AbstractContext"]

type 'a univ_abstracted = {
  univ_abstracted_value : 'a;
  univ_abstracted_binder : AbstractContext.t;
}
(** A value with bound universe levels. *)

val map_univ_abstracted : ('a -> 'b) -> 'a univ_abstracted -> 'b univ_abstracted

(** Universe contexts (as sets) *)

(** A set of universes with universe Constraints.t.
    We linearize the set to a list after typechecking.
    Beware, representation could change.
*)

module ContextSet :
sig
  type t = Level.Set.t constrained

  val empty : t
  val is_empty : t -> bool

  val singleton : Level.t -> t
  val of_instance : Instance.t -> t
  val of_set : Level.Set.t -> t

  val equal : t -> t -> bool
  val union : t -> t -> t

  val append : t -> t -> t
  (** Variant of {!union} which is more efficient when the left argument is
      much smaller than the right one. *)

  val diff : t -> t -> t
  val add_universe : Level.t -> t -> t
  val add_constraints : Constraints.t -> t -> t
  val add_instance : Instance.t -> t -> t

  val sort_levels : Level.t array -> Level.t array
  (** Arbitrary choice of linear order of the variables *)

  val to_context : (Instance.t -> Names.Name.t array) -> t -> UContext.t
  (** Build a vector of universe levels assuming a function generating names *)

  val of_context : UContext.t -> t

  val constraints : t -> Constraints.t
  val levels : t -> Level.Set.t

  val size : t -> int
  (** The number of universes in the context *)

end

(** A value in a universe context (resp. context set). *)
type 'a in_universe_context = 'a * UContext.t
type 'a in_universe_context_set = 'a * ContextSet.t

val extend_in_context_set : 'a in_universe_context_set -> ContextSet.t ->
  'a in_universe_context_set

val empty_level_subst : universe_level_subst
val is_empty_level_subst : universe_level_subst -> bool

val lift_level_subst : int -> universe_level_subst -> universe_level_subst
(** Lift de Bruijn universe variables (Var) in the substitution *)

val merge_level_subst : universe_level_subst -> universe_level_subst -> universe_level_subst
(** Merge two substitutions assumed to have disjoint domains *)

(** Substitution of universes. *)
val subst_univs_level_level : universe_level_subst -> Level.t -> Level.t
val subst_univs_level_universe : universe_level_subst -> Universe.t -> Universe.t
val subst_univs_level_constraints : universe_level_subst -> Constraints.t -> Constraints.t
val subst_univs_level_abstract_universe_context :
  universe_level_subst -> AbstractContext.t -> AbstractContext.t
val subst_univs_level_instance : universe_level_subst -> Instance.t -> Instance.t

(** Level to universe substitutions. *)

val make_subst : universe_subst -> universe_subst_fn

val subst_univs_universe : universe_subst_fn -> Universe.t -> Universe.t
(** Only user in the kernel is template polymorphism. Ideally we get rid of
    this code if it goes away. *)

(** Substitution of instances *)
val subst_instance_instance : Instance.t -> Instance.t -> Instance.t
val subst_instance_universe : Instance.t -> Universe.t -> Universe.t

val make_instance_subst : Instance.t -> universe_level_subst
(** Creates [u(0) ↦ 0; ...; u(n-1) ↦ n - 1] out of [u(0); ...; u(n - 1)] *)

val make_inverse_instance_subst : Instance.t -> universe_level_subst

val abstract_universes : UContext.t -> Instance.t * AbstractContext.t
(** TODO: move universe abstraction out of the kernel *)

val make_abstract_instance : AbstractContext.t -> Instance.t

(** [compact_univ u] remaps local variables in [u] such that their indices become
     consecutive. It returns the new universe and the mapping.
     Example: compact_univ [(Var 0, i); (Prop, 0); (Var 2; j))] =
       [(Var 0,i); (Prop, 0); (Var 1; j)], [0; 2]
*)
val compact_univ : Universe.t -> Universe.t * int list

(** {6 Pretty-printing of universes. } *)

val pr_constraint_type : constraint_type -> Pp.t
val pr_constraints : (Level.t -> Pp.t) -> Constraints.t -> Pp.t
val pr_universe_context : (Level.t -> Pp.t) -> ?variance:Variance.t array ->
  UContext.t -> Pp.t
val pr_abstract_universe_context : (Level.t -> Pp.t) -> ?variance:Variance.t array ->
  AbstractContext.t -> Pp.t
val pr_universe_context_set : (Level.t -> Pp.t) -> ContextSet.t -> Pp.t
val explain_universe_inconsistency : (Level.t -> Pp.t) ->
  univ_inconsistency -> Pp.t

val pr_universe_level_subst : universe_level_subst -> Pp.t
val pr_universe_subst : universe_subst -> Pp.t

(** {6 Hash-consing } *)

val hcons_univ : Universe.t -> Universe.t
val hcons_constraints : Constraints.t -> Constraints.t
val hcons_universe_set : Level.Set.t -> Level.Set.t
val hcons_universe_context : UContext.t -> UContext.t
val hcons_abstract_universe_context : AbstractContext.t -> AbstractContext.t
val hcons_universe_context_set : ContextSet.t -> ContextSet.t
