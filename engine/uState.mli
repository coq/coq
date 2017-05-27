(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This file defines universe unification states which are part of evarmaps.
    Most of the API below is reexported in {!Evd}. Consider using higher-level
    primitives when needed. *)

open Names

exception UniversesDiffer

type t
(** Type of universe unification states. They allow the incremental building of
    universe constraints during an interactive proof. *)

(** {5 Constructors} *)

val empty : t

val make : UGraph.t -> t

val is_empty : t -> bool

val union : t -> t -> t

val of_context_set : Univ.universe_context_set -> t

val of_binders : Universes.universe_binders -> t

(** {5 Projections} *)

val context_set : t -> Univ.universe_context_set
(** The local context of the state, i.e. a set of bound variables together
    with their associated constraints. *)

val subst : t -> Universes.universe_opt_subst
(** The local universes that are unification variables *)

val ugraph : t -> UGraph.t
(** The current graph extended with the local constraints *)

val initial_graph : t -> UGraph.t
(** The initial graph with just the declarations of new universes. *)

val algebraics : t -> Univ.LSet.t
(** The subset of unification variables that can be instantiated with algebraic
    universes as they appear in inferred types only. *)

val constraints : t -> Univ.constraints
(** Shorthand for {!context_set} composed with {!ContextSet.constraints}. *)

val context : t -> Univ.universe_context
(** Shorthand for {!context_set} with {!Context_set.to_context}. *)

(** {5 Constraints handling} *)

val add_constraints : t -> Univ.constraints -> t
(**
  @raise UniversesDiffer when universes differ
*)

val add_universe_constraints : t -> Universes.universe_constraints -> t
(**
  @raise UniversesDiffer when universes differ
*)

(** {5 Names} *)

val add_universe_name : t -> string -> Univ.Level.t -> t
(** Associate a human-readable name to a local variable. *)

val universe_of_name : t -> string -> Univ.Level.t
(** Retrieve the universe associated to the name. *)

(** {5 Unification} *)

val restrict : t -> Univ.universe_set -> t

type rigid = 
  | UnivRigid
  | UnivFlexible of bool (** Is substitution by an algebraic ok? *)

val univ_rigid : rigid
val univ_flexible : rigid
val univ_flexible_alg : rigid

val merge : ?loc:Loc.t -> bool -> rigid -> t -> Univ.universe_context_set -> t
val merge_subst : t -> Universes.universe_opt_subst -> t
val emit_side_effects : Safe_typing.private_constants -> t -> t

val new_univ_variable : ?loc:Loc.t -> rigid -> string option -> t -> t * Univ.Level.t
val add_global_univ : t -> Univ.Level.t -> t
val make_flexible_variable : t -> bool -> Univ.Level.t -> t

val is_sort_variable : t -> Sorts.t -> Univ.Level.t option

val normalize_variables : t -> Univ.universe_subst * t

val constrain_variables : Univ.LSet.t -> t -> Univ.constraints

val abstract_undefined_variables : t -> t

val fix_undefined_variables : t -> t

val refresh_undefined_univ_variables : t -> t * Univ.universe_level_subst

val normalize : t -> t

(** {5 TODO: Document me} *)

val universe_context : ?names:(Id.t Loc.located) list -> t -> (Id.t * Univ.Level.t) list * Univ.universe_context

val update_sigma_env : t -> Environ.env -> t

(** {5 Pretty-printing} *)

val pr_uctx_level : t -> Univ.Level.t -> Pp.std_ppcmds
