(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Evd
open Environ
open Namegen
open EConstr

(** This module provides useful higher-level functions for evar manipulation. *)

(** {6 Metas} *)

(** [new_meta] is a generator of unique meta variables *)
val new_meta : unit -> metavariable

(** {6 Creating a fresh evar given their type and context} *)

val next_evar_name : evar_map -> intro_pattern_naming_expr -> Id.t option

module VarSet :
sig
  type t
  val empty : t
  val full : t
  val variables : Environ.env -> t
end

type naming_mode =
  | RenameExistingBut of VarSet.t
  | FailIfConflict
  | ProgramNaming of VarSet.t

val new_evar :
  ?src:Evar_kinds.t Loc.located -> ?filter:Filter.t ->
  ?relevance:ERelevance.t ->
  ?abstract_arguments:Abstraction.t -> ?candidates:constr list ->
  ?naming:intro_pattern_naming_expr ->
  ?typeclass_candidate:bool ->
  ?hypnaming:naming_mode ->
  env -> evar_map -> types -> evar_map * EConstr.t

(** Alias of {!Evd.new_pure_evar} *)
val new_pure_evar :
  ?src:Evar_kinds.t Loc.located -> ?filter:Filter.t ->
  relevance:ERelevance.t ->
  ?abstract_arguments:Abstraction.t -> ?candidates:constr list ->
  ?name:Id.t ->
  ?typeclass_candidate:bool ->
  named_context_val -> evar_map -> types -> evar_map * Evar.t

(** Create a new Type existential variable, as we keep track of
    them during type-checking and unification. *)
val new_type_evar :
  ?src:Evar_kinds.t Loc.located -> ?filter:Filter.t ->
  ?naming:intro_pattern_naming_expr ->
  ?hypnaming:naming_mode ->
  env -> evar_map -> rigid ->
  evar_map * (constr * ESorts.t)

val new_Type : ?rigid:rigid -> evar_map -> evar_map * constr

(** {6 Unification utils} *)

(* Expand head evar if any *)
val whd_head_evar :  evar_map -> constr -> constr

(* An over-approximation of [has_undefined (nf_evars evd c)] *)
val has_undefined_evars : evar_map -> constr -> bool
val has_undefined_evars_or_metas : evar_map -> constr -> bool

val is_ground_term :  evar_map -> constr -> bool
val is_ground_env  :  evar_map -> env -> bool

(** [advance sigma g] returns [Some g'] if [g'] is undefined and is
    the current avatar of [g] (for instance [g] was changed by [clear]
    into [g']). It returns [None] if [g] has been (partially)
    solved. *)
val advance : evar_map -> Evar.t -> Evar.t option

(** [reachable_from_evars sigma seeds] computes the descendents of
    evars in [seeds] by restriction or evar-evar unifications in [sigma]. *)
val reachable_from_evars : evar_map -> Evar.Set.t -> Evar.Set.t

(** The following functions return the set of undefined evars
    contained in the object, the defined evars being traversed.
    This is roughly a combination of the previous functions and
    [nf_evar]. *)

val undefined_evars_of_term : evar_map -> constr -> Evar.Set.t
val undefined_evars_of_named_context : evar_map -> Constr.named_context -> Evar.Set.t

type undefined_evars_cache

val create_undefined_evars_cache : unit -> undefined_evars_cache

val filtered_undefined_evars_of_evar_info : ?cache:undefined_evars_cache -> evar_map -> 'a evar_info -> Evar.Set.t

(** [occur_evar_upto sigma k c] returns [true] if [k] appears in
    [c]. It looks up recursively in [sigma] for the value of existential
    variables. *)
val occur_evar_upto : evar_map -> Evar.t -> constr -> bool

(** {6 Value/Type constraints} *)

val judge_of_new_Type : evar_map -> evar_map * unsafe_judgment

(***********************************************************)

val create_clos_infos : env -> evar_map -> RedFlags.reds -> CClosure.clos_infos

val whd_evar :  evar_map -> constr -> constr
val nf_evar :  evar_map -> constr -> constr
val j_nf_evar :  evar_map -> unsafe_judgment -> unsafe_judgment
val jl_nf_evar :
   evar_map -> unsafe_judgment list -> unsafe_judgment list
val jv_nf_evar :
   evar_map -> unsafe_judgment array -> unsafe_judgment array
val tj_nf_evar :
   evar_map -> unsafe_type_judgment -> unsafe_type_judgment

val nf_named_context_evar : evar_map -> Constr.named_context -> Constr.named_context
val nf_rel_context_evar : evar_map -> rel_context -> rel_context
val nf_env_evar : evar_map -> env -> env

val nf_evar_info : evar_map -> 'a evar_info -> 'a evar_info
val nf_evar_map : evar_map -> evar_map
val nf_evar_map_undefined : evar_map -> evar_map
val nf_relevance : evar_map -> Sorts.relevance -> Sorts.relevance

(** Presenting terms without solved evars *)

val nf_evars_universes : evar_map -> Constr.constr -> Constr.constr

(** [finalize env sigma f] combines universe minimisation,
   evar-and-universe normalisation and universe restriction.

    It minimizes universes in [sigma], calls [f] a normalisation
   function with respect to the updated [sigma] and restricts the
   local universes of [sigma] to those encountered while running [f].

    Note that the normalizer passed to [f] holds some imperative state
   in its closure. *)
val finalize : ?abort_on_undefined_evars:bool -> evar_map ->
  ((EConstr.t -> Constr.t) -> 'a) ->
  evar_map * 'a

(** {6 Term manipulation up to instantiation} *)

(** Like {!Constr.kind} except that [kind_of_term sigma t] exposes [t]
    as an evar [e] only if [e] is uninstantiated in [sigma]. Otherwise the
    value of [e] in [sigma] is (recursively) used. *)
val kind_of_term_upto : evar_map -> Constr.constr ->
  (Constr.constr, Constr.types, Sorts.t, UVars.Instance.t, Sorts.relevance) kind_of_term

(** [eq_constr_univs_test ~evd ~extended_evd t u] tests equality of
    [t] and [u] up to existential variable instantiation and
    equalisable universes. The term [t] is interpreted in [evd] while
    [u] is interpreted in [extended_evd]. The universe constraints in
    [extended_evd] are assumed to be an extension of those in [evd]. *)
val eq_constr_univs_test :
    evd:Evd.evar_map ->
    extended_evd:Evd.evar_map ->
    constr ->
    constr ->
    bool

(** [compare_cumulative_instances cv_pb variance u1 u2 sigma] Returns
   [Inl sigma'] where [sigma'] is [sigma] augmented with universe
   constraints such that [u1 cv_pb? u2] according to [variance].
   Additionally flexible universes in irrelevant positions are unified
   if possible. Returns [Inr p] when the former is impossible. *)
val compare_cumulative_instances : Conversion.conv_pb -> UVars.Variance.t array ->
  UVars.Instance.t -> UVars.Instance.t -> evar_map ->
  (evar_map, UGraph.univ_inconsistency) Util.union

(** We should only compare constructors at convertible types, so this
    is only an opportunity to unify universes.

    But what about qualities?
*)
val compare_constructor_instances : evar_map ->
  UVars.Instance.t -> UVars.Instance.t -> (evar_map, UGraph.univ_inconsistency) Util.union

(** {6 Unification problems} *)
type unification_pb = conv_pb * env * constr * constr

(** [add_unification_pb ?tail pb sigma]
    Add a unification problem [pb] to [sigma], if not already present.
    Put it at the end of the list if [tail] is true, by default it is false. *)
val add_unification_pb : ?tail:bool -> unification_pb -> evar_map -> evar_map

(** {6 Removing hyps in evars'context}
raise OccurHypInSimpleClause if the removal breaks dependencies *)

type clear_dependency_error =
| OccurHypInSimpleClause of Id.t option
| EvarTypingBreak of EConstr.existential
| NoCandidatesLeft of Evar.t

exception ClearDependencyError of Id.t * clear_dependency_error * GlobRef.t option

(** Restrict an undefined evar according to a (sub)filter and candidates.
    The evar will be defined if there is only one candidate left,
    @raise ClearDependencyError NoCandidatesLeft if the filter turns the candidates
    into an empty list. *)

val restrict_evar : evar_map -> Evar.t -> Filter.t ->
  constr list option -> evar_map * Evar.t

val clear_hyps_in_evi : env -> evar_map -> named_context_val -> types ->
  Id.Set.t -> evar_map * named_context_val * types

val clear_hyps2_in_evi : env -> evar_map -> named_context_val -> types -> types ->
  Id.Set.t -> evar_map * named_context_val * types * types

val check_and_clear_in_constr
  : Environ.env
  -> Evd.evar_map
  -> clear_dependency_error
  -> Names.Id.Set.t
  -> EConstr.constr
  -> Evd.evar_map

type csubst

val empty_csubst : csubst
val csubst_subst : Evd.evar_map -> csubst -> constr -> constr

type ext_named_context =
  csubst * Id.Set.t * named_context_val

val default_ext_instance : ext_named_context -> constr SList.t

val push_rel_decl_to_named_context : hypnaming:naming_mode ->
  evar_map -> rel_declaration -> ext_named_context -> ext_named_context

val push_rel_context_to_named_context : hypnaming:naming_mode ->
  Environ.env -> evar_map -> types ->
  named_context_val * types * constr SList.t * csubst

val generalize_evar_over_rels : evar_map -> existential -> types * constr list

val subterm_source : Evar.t -> ?where:Evar_kinds.subevar_kind -> Evar_kinds.t Loc.located ->
  Evar_kinds.t Loc.located

val meta_counter_summary_tag : int Summary.Dyn.tag
