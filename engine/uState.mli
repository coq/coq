(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Universe unification states *)

open Names

exception UniversesDiffer

type t

(** {5 Constructors} *)

val empty : t

val from : Environ.env -> t

val make : Environ.env -> Id.t Loc.located list option -> t

val is_empty : t -> bool

val union : t -> t -> t

val of_context_set : Univ.universe_context_set -> t

(** {5 Projections} *)

val context_set : Univ.universe_context -> t -> Univ.universe_context_set
val constraints : t -> Univ.constraints
val context : t -> Univ.universe_context
val subst : t -> Universes.universe_opt_subst
val ugraph : t -> UGraph.t
val variables : t -> Univ.LSet.t

(** {5 Constraints handling} *)

val add_constraints : t -> Univ.constraints -> t
val add_universe_constraints : t -> Universes.universe_constraints -> t

(** {5 TODO: Document me} *)

val universe_context : ?names:(Id.t Loc.located) list -> t -> Univ.universe_context

val pr_uctx_level : t -> Univ.Level.t -> Pp.std_ppcmds

val restrict : t -> Univ.universe_set -> t

type rigid = 
  | UnivRigid
  | UnivFlexible of bool (** Is substitution by an algebraic ok? *)

val univ_rigid : rigid
val univ_flexible : rigid
val univ_flexible_alg : rigid

val merge : bool -> rigid -> t -> Univ.universe_context_set -> t
val merge_subst : t -> Universes.universe_opt_subst -> t
val emit_side_effects : Declareops.side_effects -> t -> t

val new_univ_variable : rigid -> string option -> t -> t * Univ.Level.t
val add_global_univ : t -> Univ.Level.t -> t
val make_flexible_variable : t -> bool -> Univ.Level.t -> t

val is_sort_variable : t -> Sorts.t -> Univ.Level.t option

val normalize_variables : t -> Univ.universe_subst * t

val abstract_undefined_variables : t -> t

val fix_undefined_variables : t -> t

val refresh_undefined_univ_variables : t -> t * Univ.universe_level_subst

val normalize : t -> t

val universe_of_name : t -> string -> Univ.Level.t

val add_universe_name : t -> string -> Univ.Level.t -> t
