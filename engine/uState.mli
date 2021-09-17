(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file defines universe unification states which are part of evarmaps.
    Most of the API below is reexported in {!Evd}. Consider using higher-level
    primitives when needed. *)

open Names
open Univ

type universes_entry =
| Monomorphic_entry of Univ.ContextSet.t
| Polymorphic_entry of Univ.UContext.t

exception UniversesDiffer

type t
(** Type of universe unification states. They allow the incremental building of
    universe constraints during an interactive proof. *)

(** {5 Constructors} *)

(** Different ways to create a new universe state *)

val empty : t

val make : lbound:UGraph.Bound.t -> UGraph.t -> t
[@@ocaml.deprecated "Use from_env"]

val make_with_initial_binders : lbound:UGraph.Bound.t -> UGraph.t -> lident list -> t
[@@ocaml.deprecated "Use from_env"]

val from_env : ?binders:lident list -> Environ.env -> t
(** Main entry point at the beginning of a declaration declaring the
    binding names as rigid universes. *)

val of_binders : UnivNames.universe_binders -> t
(** Main entry point when only names matter, e.g. for printing. *)

val of_context_set : Univ.ContextSet.t -> t
(** Main entry point when starting from the instance of a global
    reference, e.g. when building a scheme. *)

(** Misc *)

val is_empty : t -> bool

val union : t -> t -> t

(** {5 Projections and other destructors} *)

val context_set : t -> Univ.ContextSet.t
(** The local context of the state, i.e. a set of bound variables together
    with their associated constraints. *)

type universe_opt_subst = UnivSubst.universe_opt_subst
(* Reexport because UnivSubst is private *)

val subst : t -> UnivSubst.universe_opt_subst
(** The local universes that are unification variables *)

val nf_universes : t -> Constr.t -> Constr.t
(** Apply the local substitution [subst] *)

val ugraph : t -> UGraph.t
(** The current graph extended with the local constraints *)

val initial_graph : t -> UGraph.t
(** The initial graph with just the declarations of new universes. *)

val algebraics : t -> Univ.Level.Set.t
(** The subset of unification variables that can be instantiated with algebraic
    universes as they appear in inferred types only. *)

val constraints : t -> Univ.Constraints.t
(** Shorthand for {!context_set} composed with {!ContextSet.constraints}. *)

val context : t -> Univ.UContext.t
(** Shorthand for {!context_set} with {!Context_set.to_context}. *)

type named_universes_entry = universes_entry * UnivNames.universe_binders

val univ_entry : poly:bool -> t -> named_universes_entry
(** Pick from {!context} or {!context_set} based on [poly]. *)

val universe_binders : t -> UnivNames.universe_binders
(** Return local names of universes. *)

(** {5 Constraints handling} *)

val add_constraints : t -> Univ.Constraints.t -> t
(**
  @raise UniversesDiffer when universes differ
*)

val add_universe_constraints : t -> UnivProblem.Set.t -> t
(**
  @raise UniversesDiffer when universes differ
*)

(** {5 Names} *)

val universe_of_name : t -> Id.t -> Univ.Level.t
(** Retrieve the universe associated to the name. *)

(** {5 Unification} *)

(** [restrict_universe_context lbound (univs,csts) keep] restricts [univs] to
   the universes in [keep]. The constraints [csts] are adjusted so
   that transitive constraints between remaining universes (those in
   [keep] and those not in [univs]) are preserved. *)
val restrict_universe_context : lbound:UGraph.Bound.t -> ContextSet.t -> Level.Set.t -> ContextSet.t

(** [restrict uctx ctx] restricts the local universes of [uctx] to
   [ctx] extended by local named universes and side effect universes
   (from [demote_seff_univs]). Transitive constraints between retained
   universes are preserved. *)
val restrict : t -> Univ.Level.Set.t -> t

type rigid =
  | UnivRigid
  | UnivFlexible of bool (** Is substitution by an algebraic ok? *)

val univ_rigid : rigid
val univ_flexible : rigid
val univ_flexible_alg : rigid

val merge : ?loc:Loc.t -> sideff:bool -> rigid -> t -> Univ.ContextSet.t -> t
val merge_subst : t -> UnivSubst.universe_opt_subst -> t
val emit_side_effects : Safe_typing.private_constants -> t -> t

val demote_global_univs : Environ.env -> t -> t
(** Removes from the uctx_local part of the UState the universes and constraints
    that are present in the universe graph in the input env (supposedly the
    global ones) *)

val demote_seff_univs : Univ.Level.Set.t -> t -> t
(** Mark the universes as not local any more, because they have been
   globally declared by some side effect. You should be using
   emit_side_effects instead. *)

val new_univ_variable : ?loc:Loc.t -> rigid -> Id.t option -> t -> t * Univ.Level.t
(** Declare a new local universe; use rigid if a global or bound
    universe; use flexible for a universe existential variable; use
    univ_flexible_alg for a universe existential variable allowed to
    be instantiated with an algebraic universe *)

val add_global_univ : t -> Univ.Level.t -> t

(** [make_flexible_variable g algebraic l]

  Turn the variable [l] flexible, and algebraic if [algebraic] is true
  and [l] can be. That is if there are no strict upper constraints on
  [l] and and it does not appear in the instance of any non-algebraic
  universe. Otherwise the variable is just made flexible.

    If [l] is already algebraic it will remain so even with [algebraic:false]. *)
val make_flexible_variable : t -> algebraic:bool -> Univ.Level.t -> t

val make_nonalgebraic_variable : t -> Univ.Level.t -> t
(** Make the level non algebraic. Undefined behaviour on
   already-defined algebraics. *)

(** Turn all undefined flexible algebraic variables into simply flexible
   ones. Can be used in case the variables might appear in universe instances
   (typically for polymorphic program obligations). *)
val make_flexible_nonalgebraic : t -> t

val is_sort_variable : t -> Sorts.t -> Univ.Level.t option

val normalize_variables : t -> t

val constrain_variables : Univ.Level.Set.t -> t -> t

val abstract_undefined_variables : t -> t

val fix_undefined_variables : t -> t

(** Universe minimization *)
val minimize : t -> t

type ('a, 'b) gen_universe_decl = {
  univdecl_instance : 'a; (* Declared universes *)
  univdecl_extensible_instance : bool; (* Can new universes be added *)
  univdecl_constraints : 'b; (* Declared constraints *)
  univdecl_extensible_constraints : bool (* Can new constraints be added *) }

type universe_decl =
  (lident list, Univ.Constraints.t) gen_universe_decl

val default_univ_decl : universe_decl

(** [check_univ_decl ctx decl]

   If non extensible in [decl], check that the local universes (resp.
   universe constraints) in [ctx] are implied by [decl].

   Return a [universes_entry] containing the local
   universes of [ctx] and their constraints.

   When polymorphic, the universes corresponding to
   [decl.univdecl_instance] come first in the order defined by that
   list. *)
val check_univ_decl : poly:bool -> t -> universe_decl -> named_universes_entry

val check_mono_univ_decl : t -> universe_decl -> Univ.ContextSet.t

(** {5 TODO: Document me} *)

val update_sigma_univs : t -> UGraph.t -> t

(** {5 Pretty-printing} *)

val pr_uctx_level : t -> Univ.Level.t -> Pp.t
val qualid_of_level : t -> Univ.Level.t -> Libnames.qualid option

(** Only looks in the local names, not in the nametab. *)
val id_of_level : t -> Univ.Level.t -> Id.t option

val pr_weak : (Univ.Level.t -> Pp.t) -> t -> Pp.t

val pr_universe_opt_subst : universe_opt_subst -> Pp.t
