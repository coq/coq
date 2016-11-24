(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Evd
open Environ

(** This module provides useful higher-level functions for evar manipulation. *)

(** {6 Metas} *)

(** [new_meta] is a generator of unique meta variables *)
val new_meta : unit -> metavariable
val mk_new_meta : unit -> EConstr.constr

(** {6 Creating a fresh evar given their type and context} *)
val new_evar :
  env -> 'r Sigma.t -> ?src:Loc.t * Evar_kinds.t -> ?filter:Filter.t ->
  ?candidates:EConstr.constr list -> ?store:Store.t ->
  ?naming:Misctypes.intro_pattern_naming_expr ->
  ?principal:bool -> EConstr.types -> (EConstr.constr, 'r) Sigma.sigma

val new_pure_evar :
  named_context_val -> 'r Sigma.t -> ?src:Loc.t * Evar_kinds.t -> ?filter:Filter.t ->
  ?candidates:EConstr.constr list -> ?store:Store.t ->
  ?naming:Misctypes.intro_pattern_naming_expr ->
  ?principal:bool -> EConstr.types -> (evar, 'r) Sigma.sigma

val new_pure_evar_full : 'r Sigma.t -> evar_info -> (evar, 'r) Sigma.sigma

(** the same with side-effects *)
val e_new_evar :
  env -> evar_map ref -> ?src:Loc.t * Evar_kinds.t -> ?filter:Filter.t ->
  ?candidates:EConstr.constr list -> ?store:Store.t ->
  ?naming:Misctypes.intro_pattern_naming_expr ->
  ?principal:bool -> EConstr.types -> EConstr.constr

(** Create a new Type existential variable, as we keep track of 
    them during type-checking and unification. *)
val new_type_evar :
  env -> 'r Sigma.t -> ?src:Loc.t * Evar_kinds.t -> ?filter:Filter.t ->
  ?naming:Misctypes.intro_pattern_naming_expr -> ?principal:bool -> rigid ->
  (EConstr.constr * sorts, 'r) Sigma.sigma

val e_new_type_evar : env -> evar_map ref ->
  ?src:Loc.t * Evar_kinds.t -> ?filter:Filter.t ->
  ?naming:Misctypes.intro_pattern_naming_expr -> ?principal:bool -> rigid -> EConstr.constr * sorts

val new_Type : ?rigid:rigid -> env -> 'r Sigma.t -> (EConstr.constr, 'r) Sigma.sigma
val e_new_Type : ?rigid:rigid -> env -> evar_map ref -> EConstr.constr

val restrict_evar : 'r Sigma.t -> existential_key -> Filter.t ->
  EConstr.constr list option -> (existential_key, 'r) Sigma.sigma

(** Polymorphic constants *)

val new_global : 'r Sigma.t -> Globnames.global_reference -> (EConstr.constr, 'r) Sigma.sigma
val e_new_global : evar_map ref -> Globnames.global_reference -> EConstr.constr

(** Create a fresh evar in a context different from its definition context:
   [new_evar_instance sign evd ty inst] creates a new evar of context
   [sign] and type [ty], [inst] is a mapping of the evar context to
   the context where the evar should occur. This means that the terms
   of [inst] are typed in the occurrence context and their type (seen
   as a telescope) is [sign] *)
val new_evar_instance :
 named_context_val -> 'r Sigma.t -> EConstr.types -> 
  ?src:Loc.t * Evar_kinds.t -> ?filter:Filter.t -> ?candidates:EConstr.constr list ->
  ?store:Store.t -> ?naming:Misctypes.intro_pattern_naming_expr ->
  ?principal:bool ->
  EConstr.constr list -> (EConstr.constr, 'r) Sigma.sigma

val make_pure_subst : evar_info -> 'a array -> (Id.t * 'a) list

val safe_evar_value : evar_map -> existential -> constr option

(** {6 Evars/Metas switching...} *)

val non_instantiated : evar_map -> evar_info Evar.Map.t

(** {6 Unification utils} *)

(** [head_evar c] returns the head evar of [c] if any *)
exception NoHeadEvar
val head_evar : evar_map -> EConstr.constr -> existential_key (** may raise NoHeadEvar *)

(* Expand head evar if any *)
val whd_head_evar :  evar_map -> EConstr.constr -> EConstr.constr

(* An over-approximation of [has_undefined (nf_evars evd c)] *)
val has_undefined_evars : evar_map -> EConstr.constr -> bool

val is_ground_term :  evar_map -> EConstr.constr -> bool
val is_ground_env  :  evar_map -> env -> bool

(** [gather_dependent_evars evm seeds] classifies the evars in [evm]
    as dependent_evars and goals (these may overlap). A goal is an
    evar in [seeds] or an evar appearing in the (partial) definition
    of a goal. A dependent evar is an evar appearing in the type
    (hypotheses and conclusion) of a goal, or in the type or (partial)
    definition of a dependent evar.  The value return is a map
    associating to each dependent evar [None] if it has no (partial)
    definition or [Some s] if [s] is the list of evars appearing in
    its (partial) definition. *)
val gather_dependent_evars : evar_map -> evar list -> (Evar.Set.t option) Evar.Map.t

(** [advance sigma g] returns [Some g'] if [g'] is undefined and is
    the current avatar of [g] (for instance [g] was changed by [clear]
    into [g']). It returns [None] if [g] has been (partially)
    solved. *)
val advance : evar_map -> evar -> evar option

(** The following functions return the set of undefined evars
    contained in the object, the defined evars being traversed.
    This is roughly a combination of the previous functions and
    [nf_evar]. *)

val undefined_evars_of_term : evar_map -> EConstr.constr -> Evar.Set.t
val undefined_evars_of_named_context : evar_map -> Context.Named.t -> Evar.Set.t
val undefined_evars_of_evar_info : evar_map -> evar_info -> Evar.Set.t

(** [occur_evar_upto sigma k c] returns [true] if [k] appears in
    [c]. It looks up recursively in [sigma] for the value of existential
    variables. *)
val occur_evar_upto : evar_map -> Evar.t -> EConstr.t -> bool

(** {6 Value/Type constraints} *)

val judge_of_new_Type : 'r Sigma.t -> (unsafe_judgment, 'r) Sigma.sigma

(***********************************************************)

(** [flush_and_check_evars] raise [Uninstantiated_evar] if an evar remains
    uninstantiated; [nf_evar] leaves uninstantiated evars as is *)

val whd_evar :  evar_map -> constr -> constr
val nf_evar :  evar_map -> constr -> constr
val j_nf_evar :  evar_map -> EConstr.unsafe_judgment -> EConstr.unsafe_judgment
val jl_nf_evar :
   evar_map -> EConstr.unsafe_judgment list -> EConstr.unsafe_judgment list
val jv_nf_evar :
   evar_map -> EConstr.unsafe_judgment array -> EConstr.unsafe_judgment array
val tj_nf_evar :
   evar_map -> EConstr.unsafe_type_judgment -> EConstr.unsafe_type_judgment

val nf_named_context_evar : evar_map -> Context.Named.t -> Context.Named.t
val nf_rel_context_evar : evar_map -> Context.Rel.t -> Context.Rel.t
val nf_env_evar : evar_map -> env -> env

val nf_evar_info : evar_map -> evar_info -> evar_info
val nf_evar_map : evar_map -> evar_map
val nf_evar_map_undefined : evar_map -> evar_map

(** Presenting terms without solved evars *)

val nf_evars_universes : evar_map -> constr -> constr

val nf_evars_and_universes : evar_map -> evar_map * (constr -> constr)
val e_nf_evars_and_universes : evar_map ref -> (constr -> constr) * Universes.universe_opt_subst

(** Normalize the evar map w.r.t. universes, after simplification of constraints.
    Return the substitution function for constrs as well. *)
val nf_evar_map_universes : evar_map -> evar_map * (constr -> constr)

(** Replacing all evars, possibly raising [Uninstantiated_evar] *)
exception Uninstantiated_evar of existential_key
val flush_and_check_evars :  evar_map -> EConstr.constr -> constr

(** {6 Term manipulation up to instantiation} *)

(** Like {!Constr.kind} except that [kind_of_term sigma t] exposes [t]
    as an evar [e] only if [e] is uninstantiated in [sigma]. Otherwise the
    value of [e] in [sigma] is (recursively) used. *)
val kind_of_term_upto : evar_map -> constr -> (constr,types) kind_of_term

(** [eq_constr_univs_test sigma1 sigma2 t u] tests equality of [t] and
    [u] up to existential variable instantiation and equalisable
    universes. The term [t] is interpreted in [sigma1] while [u] is
    interpreted in [sigma2]. The universe constraints in [sigma2] are
    assumed to be an extention of those in [sigma1]. *)
val eq_constr_univs_test : evar_map -> evar_map -> constr -> constr -> bool

(** {6 Removing hyps in evars'context}
raise OccurHypInSimpleClause if the removal breaks dependencies *)

type clear_dependency_error =
| OccurHypInSimpleClause of Id.t option
| EvarTypingBreak of existential

exception ClearDependencyError of Id.t * clear_dependency_error

(* spiwack: marks an evar that has been "defined" by clear.
    used by [Goal] and (indirectly) [Proofview] to handle the clear tactic gracefully*)
val cleared : bool Store.field

val clear_hyps_in_evi : env -> evar_map ref -> named_context_val -> EConstr.types ->
  Id.Set.t -> named_context_val * types

val clear_hyps2_in_evi : env -> evar_map ref -> named_context_val -> types -> types ->
  Id.Set.t -> named_context_val * types * types

type csubst

val empty_csubst : csubst
val csubst_subst : csubst -> EConstr.t -> EConstr.t

type ext_named_context =
  csubst * (Id.t * EConstr.constr) list *
  Id.Set.t * Context.Named.t

val push_rel_decl_to_named_context :
  Context.Rel.Declaration.t -> ext_named_context -> ext_named_context

val push_rel_context_to_named_context : Environ.env -> EConstr.types ->
  named_context_val * EConstr.types * EConstr.constr list * csubst * (identifier*EConstr.constr) list

val generalize_evar_over_rels : evar_map -> EConstr.existential -> EConstr.types * EConstr.constr list

(** Evar combinators *)

val evd_comb0 : (evar_map -> evar_map * 'a) -> evar_map ref -> 'a
val evd_comb1 : (evar_map -> 'b -> evar_map * 'a) -> evar_map ref -> 'b -> 'a
val evd_comb2 : (evar_map -> 'b -> 'c -> evar_map * 'a) -> evar_map ref -> 'b -> 'c -> 'a

val subterm_source : existential_key -> Evar_kinds.t Loc.located ->
  Evar_kinds.t Loc.located

val meta_counter_summary_name : string

(** Deprecater *)

type type_constraint = EConstr.types option
type val_constraint = EConstr.constr option
