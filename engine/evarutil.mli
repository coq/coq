(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
val mk_new_meta : unit -> constr

(** {6 Creating a fresh evar given their type and context} *)

val new_evar_from_context :
  ?src:Evar_kinds.t Loc.located -> ?filter:Filter.t ->
  ?candidates:constr list -> ?store:Store.t ->
  ?naming:intro_pattern_naming_expr ->
  ?principal:bool ->
  named_context_val -> evar_map  -> types -> evar_map * EConstr.t

type naming_mode =
  | KeepUserNameAndRenameExistingButSectionNames
  | KeepUserNameAndRenameExistingEvenSectionNames
  | KeepExistingNames
  | FailIfConflict

val new_evar :
  ?src:Evar_kinds.t Loc.located -> ?filter:Filter.t ->
  ?candidates:constr list -> ?store:Store.t ->
  ?naming:intro_pattern_naming_expr ->
  ?principal:bool -> ?hypnaming:naming_mode ->
  env -> evar_map -> types -> evar_map * EConstr.t

val new_pure_evar :
  ?src:Evar_kinds.t Loc.located -> ?filter:Filter.t ->
  ?candidates:constr list -> ?store:Store.t ->
  ?naming:intro_pattern_naming_expr ->
  ?principal:bool ->
  named_context_val -> evar_map -> types -> evar_map * Evar.t

val new_pure_evar_full : evar_map -> evar_info -> evar_map * Evar.t

(** Create a new Type existential variable, as we keep track of 
    them during type-checking and unification. *)
val new_type_evar :
  ?src:Evar_kinds.t Loc.located -> ?filter:Filter.t ->
  ?naming:intro_pattern_naming_expr ->
  ?principal:bool -> ?hypnaming:naming_mode ->
  env -> evar_map -> rigid ->
  evar_map * (constr * Sorts.t)

val new_Type : ?rigid:rigid -> evar_map -> evar_map * constr

(** Polymorphic constants *)

val new_global : evar_map -> GlobRef.t -> evar_map * constr

(** Create a fresh evar in a context different from its definition context:
   [new_evar_instance sign evd ty inst] creates a new evar of context
   [sign] and type [ty], [inst] is a mapping of the evar context to
   the context where the evar should occur. This means that the terms
   of [inst] are typed in the occurrence context and their type (seen
   as a telescope) is [sign] *)
val new_evar_instance :
  ?src:Evar_kinds.t Loc.located -> ?filter:Filter.t -> ?candidates:constr list ->
  ?store:Store.t -> ?naming:intro_pattern_naming_expr ->
  ?principal:bool ->
 named_context_val -> evar_map -> types ->
  constr list -> evar_map * constr

val make_pure_subst : evar_info -> 'a array -> (Id.t * 'a) list

val safe_evar_value : evar_map -> Constr.existential -> Constr.constr option

(** {6 Evars/Metas switching...} *)

val non_instantiated : evar_map -> evar_info Evar.Map.t

(** {6 Unification utils} *)

(** [head_evar c] returns the head evar of [c] if any *)
exception NoHeadEvar
val head_evar : evar_map -> constr -> Evar.t (** may raise NoHeadEvar *)

(* Expand head evar if any *)
val whd_head_evar :  evar_map -> constr -> constr

(* An over-approximation of [has_undefined (nf_evars evd c)] *)
val has_undefined_evars : evar_map -> constr -> bool

val is_ground_term :  evar_map -> constr -> bool
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
val gather_dependent_evars : evar_map -> Evar.t list -> (Evar.Set.t option) Evar.Map.t

(** [advance sigma g] returns [Some g'] if [g'] is undefined and is
    the current avatar of [g] (for instance [g] was changed by [clear]
    into [g']). It returns [None] if [g] has been (partially)
    solved. *)
val advance : evar_map -> Evar.t -> Evar.t option

(** The following functions return the set of undefined evars
    contained in the object, the defined evars being traversed.
    This is roughly a combination of the previous functions and
    [nf_evar]. *)

val undefined_evars_of_term : evar_map -> constr -> Evar.Set.t
val undefined_evars_of_named_context : evar_map -> Constr.named_context -> Evar.Set.t
val undefined_evars_of_evar_info : evar_map -> evar_info -> Evar.Set.t

type undefined_evars_cache

val create_undefined_evars_cache : unit -> undefined_evars_cache

val filtered_undefined_evars_of_evar_info : ?cache:undefined_evars_cache -> evar_map -> evar_info -> Evar.Set.t

(** [occur_evar_upto sigma k c] returns [true] if [k] appears in
    [c]. It looks up recursively in [sigma] for the value of existential
    variables. *)
val occur_evar_upto : evar_map -> Evar.t -> constr -> bool

(** {6 Value/Type constraints} *)

val judge_of_new_Type : evar_map -> evar_map * unsafe_judgment

(***********************************************************)

(** [flush_and_check_evars] raise [Uninstantiated_evar] if an evar remains
    uninstantiated; [nf_evar] leaves uninstantiated evars as is *)

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

val nf_evar_info : evar_map -> evar_info -> evar_info
val nf_evar_map : evar_map -> evar_map
val nf_evar_map_undefined : evar_map -> evar_map

(** Presenting terms without solved evars *)

val nf_evars_universes : evar_map -> Constr.constr -> Constr.constr

val nf_evars_and_universes : evar_map -> evar_map * (Constr.constr -> Constr.constr)
[@@ocaml.deprecated "Use Evd.minimize_universes and nf_evars_universes"]

(** Normalize the evar map w.r.t. universes, after simplification of constraints.
    Return the substitution function for constrs as well. *)
val nf_evar_map_universes : evar_map -> evar_map * (Constr.constr -> Constr.constr)
[@@ocaml.deprecated "Use Evd.minimize_universes and nf_evar_map and nf_evars_universes"]

(** Replacing all evars, possibly raising [Uninstantiated_evar] *)
exception Uninstantiated_evar of Evar.t
val flush_and_check_evars :  evar_map -> constr -> Constr.constr

(** {6 Term manipulation up to instantiation} *)

(** Like {!Constr.kind} except that [kind_of_term sigma t] exposes [t]
    as an evar [e] only if [e] is uninstantiated in [sigma]. Otherwise the
    value of [e] in [sigma] is (recursively) used. *)
val kind_of_term_upto : evar_map -> Constr.constr ->
  (Constr.constr, Constr.types, Sorts.t, Univ.Instance.t) kind_of_term

(** [eq_constr_univs_test sigma1 sigma2 t u] tests equality of [t] and
    [u] up to existential variable instantiation and equalisable
    universes. The term [t] is interpreted in [sigma1] while [u] is
    interpreted in [sigma2]. The universe constraints in [sigma2] are
    assumed to be an extention of those in [sigma1]. *)
val eq_constr_univs_test : evar_map -> evar_map -> constr -> constr -> bool

(** [compare_cumulative_instances cv_pb variance u1 u2 sigma] Returns
   [Inl sigma'] where [sigma'] is [sigma] augmented with universe
   constraints such that [u1 cv_pb? u2] according to [variance].
   Additionally flexible universes in irrelevant positions are unified
   if possible. Returns [Inr p] when the former is impossible. *)
val compare_cumulative_instances : Reduction.conv_pb -> Univ.Variance.t array ->
  Univ.Instance.t -> Univ.Instance.t -> evar_map ->
  (evar_map, Univ.univ_inconsistency) Util.union

(** We should only compare constructors at convertible types, so this
   is only an opportunity to unify universes. *)
val compare_constructor_instances : evar_map ->
  Univ.Instance.t -> Univ.Instance.t -> evar_map

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
| EvarTypingBreak of Constr.existential
| NoCandidatesLeft of Evar.t

exception ClearDependencyError of Id.t * clear_dependency_error * GlobRef.t option

(** Restrict an undefined evar according to a (sub)filter and candidates.
    The evar will be defined if there is only one candidate left,
@raise ClearDependencyError NoCandidatesLeft if the filter turns the candidates
  into an empty list. *)

val restrict_evar : evar_map -> Evar.t -> Filter.t ->
  ?src:Evar_kinds.t Loc.located -> constr list option -> evar_map * Evar.t

val clear_hyps_in_evi : env -> evar_map -> named_context_val -> types ->
  Id.Set.t -> evar_map * named_context_val * types

val clear_hyps2_in_evi : env -> evar_map -> named_context_val -> types -> types ->
  Id.Set.t -> evar_map * named_context_val * types * types

type csubst

val empty_csubst : csubst
val csubst_subst : csubst -> constr -> constr

type ext_named_context =
  csubst * Id.Set.t * named_context

val push_rel_decl_to_named_context : ?hypnaming:naming_mode ->
  evar_map -> rel_declaration -> ext_named_context -> ext_named_context

val push_rel_context_to_named_context : ?hypnaming:naming_mode ->
  Environ.env -> evar_map -> types ->
  named_context_val * types * constr list * csubst

val generalize_evar_over_rels : evar_map -> existential -> types * constr list

(** Evar combinators *)

val evd_comb0 : (evar_map -> evar_map * 'a) -> evar_map ref -> 'a
val evd_comb1 : (evar_map -> 'b -> evar_map * 'a) -> evar_map ref -> 'b -> 'a
val evd_comb2 : (evar_map -> 'b -> 'c -> evar_map * 'a) -> evar_map ref -> 'b -> 'c -> 'a

val subterm_source : Evar.t -> ?where:Evar_kinds.subevar_kind -> Evar_kinds.t Loc.located ->
  Evar_kinds.t Loc.located

val meta_counter_summary_tag : int Summary.Dyn.tag

val e_new_evar :
  env -> evar_map ref -> ?src:Evar_kinds.t Loc.located -> ?filter:Filter.t ->
  ?candidates:constr list -> ?store:Store.t ->
  ?naming:intro_pattern_naming_expr ->
  ?principal:bool -> ?hypnaming:naming_mode -> types -> constr
[@@ocaml.deprecated "Use [Evarutil.new_evar]"]

val e_new_type_evar : env -> evar_map ref ->
  ?src:Evar_kinds.t Loc.located -> ?filter:Filter.t ->
  ?naming:intro_pattern_naming_expr ->
  ?principal:bool -> ?hypnaming:naming_mode -> rigid -> constr * Sorts.t
[@@ocaml.deprecated "Use [Evarutil.new_type_evar]"]

val e_new_Type : ?rigid:rigid -> evar_map ref -> constr
[@@ocaml.deprecated "Use [Evarutil.new_Type]"]

val e_new_global : evar_map ref -> GlobRef.t -> constr
[@@ocaml.deprecated "Use [Evarutil.new_global]"]

val e_nf_evars_and_universes : evar_map ref -> (Constr.constr -> Constr.constr) * UnivSubst.universe_opt_subst
[@@ocaml.deprecated "Use Evd.minimize_universes and nf_evars_universes"]
