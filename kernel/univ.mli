(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Universes. *)

module Level :
sig
  type t
  (** Type of universe levels. A universe level is essentially a unique name
      that will be associated to constraints later on. *)

  val set : t
  val prop : t
  val is_small : t -> bool

  val compare : t -> t -> int
  (** Comparison function *)

  val eq : t -> t -> bool
  (** Equality function *)

  (* val hash : t -> int *)
  (** Hash function *)

  val make : Names.DirPath.t -> int -> t
  (** Create a new universe level from a unique identifier and an associated
      module path. *)

  val pr : t -> Pp.std_ppcmds
end

type universe_level = Level.t
(** Alias name. *)

module LSet : 
sig 
  include Set.S with type elt = universe_level
	      
  val pr : t -> Pp.std_ppcmds
end

type universe_set = LSet.t

module LMap : 
sig
  include Map.S with type key = universe_level

  (** Favorizes the bindings in the first map. *)
  val union : 'a t -> 'a t -> 'a t
  val diff : 'a t -> 'a t -> 'a t

  val subst_union : 'a option t -> 'a option t -> 'a option t

  val elements : 'a t -> (universe_level * 'a) list
  val of_list : (universe_level * 'a) list -> 'a t
  val of_set : universe_set -> 'a -> 'a t
  val mem : universe_level -> 'a t -> bool
  val universes : 'a t -> universe_set

  val find_opt : universe_level -> 'a t -> 'a option

  val pr : ('a -> Pp.std_ppcmds) -> 'a t -> Pp.std_ppcmds
end

type 'a universe_map = 'a LMap.t

module Universe :
sig
  type t
  (** Type of universes. A universe is defined as a set of constraints w.r.t.
      other universes. *)

  val compare : t -> t -> int
  (** Comparison function *)

  val eq : t -> t -> bool
  (** Equality function *)

  (* val hash : t -> int *)
  (** Hash function *)

  val make : Level.t -> t
  (** Create a constraint-free universe out of a given level. *)

  val pr : t -> Pp.std_ppcmds

  val level : t -> Level.t option

  val levels : t -> LSet.t

  val normalize : t -> t

  (** The type of a universe *)
  val super : t -> t
    
  (** The max of 2 universes *)
  val sup   : t -> t -> t

  val type0m : t  (** image of Prop in the universes hierarchy *)
  val type0 : t  (** image of Set in the universes hierarchy *)
  val type1 : t  (** the universe of the type of Prop/Set *)
end

type universe = Universe.t

(** Alias name. *)

val pr_uni : universe -> Pp.std_ppcmds
	      
(** The universes hierarchy: Type 0- = Prop <= Type 0 = Set <= Type 1 <= ... 
   Typing of universes: Type 0-, Type 0 : Type 1; Type i : Type (i+1) if i>0 *)
val type0m_univ : universe
val type0_univ : universe
val type1_univ : universe

val is_type0_univ : universe -> bool
val is_type0m_univ : universe -> bool
val is_univ_variable : universe -> bool
val is_small_univ : universe -> bool

val sup : universe -> universe -> universe
val super : universe -> universe

val universe_level : universe -> universe_level option
val compare_levels : universe_level -> universe_level -> int
val eq_levels : universe_level -> universe_level -> bool

(** Equality of formal universe expressions. *)
val equal_universes : universe -> universe -> bool

(** {6 Graphs of universes. } *)

type universes

type 'a check_function = universes -> 'a -> 'a -> bool
val check_leq : universe check_function
val check_eq : universe check_function
val lax_check_eq : universe check_function (* same, without anomaly *)

(** The empty graph of universes *)
val empty_universes : universes

(** The initial graph of universes: Prop < Set *)
val initial_universes : universes
val is_initial_universes : universes -> bool

(** {6 Constraints. } *)

type constraint_type = Lt | Le | Eq
type univ_constraint = universe_level * constraint_type * universe_level

module Constraint : sig
 include Set.S with type elt = univ_constraint
end

type constraints = Constraint.t

val empty_constraint : constraints
val union_constraint : constraints -> constraints -> constraints
val eq_constraint : constraints -> constraints -> bool

type universe_constraint_type = ULe | UEq | ULub

type universe_constraint = universe * universe_constraint_type * universe
module UniverseConstraints : sig
  include Set.S with type elt = universe_constraint
			     
  val pr : t -> Pp.std_ppcmds
end

type universe_constraints = UniverseConstraints.t
type 'a universe_constrained = 'a * universe_constraints

(** A value with universe constraints. *)
type 'a constrained = 'a * constraints

type universe_subst_fn = universe_level -> universe
type universe_level_subst_fn = universe_level -> universe_level

(** A full substitution, might involve algebraic universes *)
type universe_subst = universe universe_map
type universe_level_subst = universe_level universe_map

val level_subst_of : universe_subst_fn -> universe_level_subst_fn

module Instance : 
sig
  type t

  val hcons : t -> t
  val empty : t
  val is_empty : t -> bool

  val eq : t -> t -> bool

  val of_array : Level.t array -> t
  val to_array : t -> Level.t array

  (** Rely on physical equality of subterms only *)
  val eqeq : t -> t -> bool

  val subst_fn : universe_level_subst_fn -> t -> t
  val subst : universe_level_subst -> t -> t

  val pr : t -> Pp.std_ppcmds

  val append : t -> t -> t

  val levels : t -> LSet.t

  val max_level : t -> int

  val check_eq : t check_function 

end

type universe_instance = Instance.t

type 'a puniverses = 'a * universe_instance
val out_punivs : 'a puniverses -> 'a
val in_punivs : 'a -> 'a puniverses

(** A list of universes with universe constraints,
    representiong local universe variables and constraints *)

module UContext :
sig 
  type t

  val make : Instance.t constrained -> t
  val empty : t
  val is_empty : t -> bool

  val instance : t -> Instance.t
  val constraints : t -> constraints

  (** Keeps the order of the instances *)
  val union : t -> t -> t

end

type universe_context = UContext.t

(** Universe contexts (as sets) *)

module ContextSet :
sig 
  type t = universe_set constrained

  val empty : t
  val is_empty : t -> bool

  val singleton : universe_level -> t
  val of_instance : Instance.t -> t
  val of_set : universe_set -> t

  val union : t -> t -> t
  val diff : t -> t -> t
  val add_constraints : t -> constraints -> t
  val add_universes : Instance.t -> t -> t

  (** Arbitrary choice of linear order of the variables 
      and normalization of the constraints *)
  val to_context : t -> universe_context
  val of_context : universe_context -> t

  val constraints : t -> constraints
  val levels : t -> universe_set
end

(** A set of universes with universe constraints.
    We linearize the set to a list after typechecking. 
    Beware, representation could change.
*)
type universe_context_set = ContextSet.t

(** A value in a universe context (resp. context set). *)
type 'a in_universe_context = 'a * universe_context
type 'a in_universe_context_set = 'a * universe_context_set

(** Constrained *)
val constraints_of : 'a constrained -> constraints


(** [check_context_subset s s'] checks that [s] is implied by [s'] as a set of constraints,
    and shrinks [s'] to the set of variables declared in [s].
. *)
val check_context_subset : universe_context_set -> universe_context -> universe_context

(** Make a universe level substitution: the list must match the context variables. *)
val make_universe_subst : Instance.t -> universe_context -> universe_subst
val empty_subst : universe_subst
val is_empty_subst : universe_subst -> bool

val empty_level_subst : universe_level_subst
val is_empty_level_subst : universe_level_subst -> bool

(** Get the instantiated graph. *)
val instantiate_univ_context : universe_subst -> universe_context -> constraints

(** Substitution of universes. *)
val subst_univs_level_level : universe_level_subst -> universe_level -> universe_level
val subst_univs_level_universe : universe_level_subst -> universe -> universe
val subst_univs_level_constraints : universe_level_subst -> constraints -> constraints

val normalize_univs_level_level : universe_level_subst -> universe_level -> universe_level

val make_subst : universe_subst -> universe_subst_fn

(* val subst_univs_level_fail : universe_subst_fn -> universe_level -> universe_level *)
val subst_univs_level : universe_subst_fn -> universe_level -> universe
val subst_univs_universe : universe_subst_fn -> universe -> universe
val subst_univs_constraints : universe_subst_fn -> constraints -> constraints
val subst_univs_universe_constraints : universe_subst_fn -> universe_constraints -> universe_constraints

(** Raises universe inconsistency if not compatible. *)
val check_consistent_constraints : universe_context_set -> constraints -> unit

type 'a constraint_function = 'a -> 'a -> constraints -> constraints

val enforce_leq : universe constraint_function
val enforce_eq : universe constraint_function
val enforce_eq_level : universe_level constraint_function
val enforce_leq_level : universe_level constraint_function
val enforce_eq_instances : universe_instance constraint_function

type 'a universe_constraint_function = 'a -> 'a -> universe_constraints -> universe_constraints

val enforce_eq_instances_univs : bool -> universe_instance universe_constraint_function

(** {6 ... } *)
(** Merge of constraints in a universes graph.
  The function [merge_constraints] merges a set of constraints in a given
  universes graph. It raises the exception [UniverseInconsistency] if the
  constraints are not satisfiable. *)

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
  constraints...
*)
type explanation = (constraint_type * universe) list
type univ_inconsistency = constraint_type * universe * universe * explanation

exception UniverseInconsistency of univ_inconsistency

val enforce_constraint : univ_constraint -> universes -> universes
val merge_constraints : constraints -> universes -> universes
val normalize_universes : universes -> universes
val sort_universes : universes -> universes

val constraints_of_universes : universes -> constraints

val to_constraints : universes -> universe_constraints -> constraints

val check_constraint  : universes -> univ_constraint -> bool
val check_constraints : constraints -> universes -> bool


(** {6 Support for sort-polymorphism } *)

val solve_constraints_system : universe option array -> universe array -> universe array ->
  universe array

val subst_large_constraint : universe -> universe -> universe -> universe

val subst_large_constraints :
  (universe * universe) list -> universe -> universe

val no_upper_constraints : universe -> constraints -> bool

(** Is u mentionned in v (or equals to v) ? *)

val univ_depends : universe -> universe -> bool

(** {6 Pretty-printing of universes. } *)

val pr_universes : universes -> Pp.std_ppcmds
val pr_constraint_type : constraint_type -> Pp.std_ppcmds
val pr_constraints : constraints -> Pp.std_ppcmds
(* val pr_universe_list : universe_list -> Pp.std_ppcmds *)
val pr_universe_context : universe_context -> Pp.std_ppcmds
val pr_universe_context_set : universe_context_set -> Pp.std_ppcmds
val pr_universe_level_subst : universe_level_subst -> Pp.std_ppcmds
val pr_universe_subst : universe_subst -> Pp.std_ppcmds
val explain_universe_inconsistency : univ_inconsistency -> Pp.std_ppcmds

(** {6 Dumping to a file } *)

val dump_universes :
  (constraint_type -> string -> string -> unit) ->
  universes -> unit

(** {6 Hash-consing } *)

val hcons_univlevel : universe_level -> universe_level
val hcons_univ : universe -> universe
val hcons_constraints : constraints -> constraints
val hcons_universe_set : universe_set -> universe_set
val hcons_universe_context : universe_context -> universe_context
val hcons_universe_context_set : universe_context_set -> universe_context_set 

(******)
