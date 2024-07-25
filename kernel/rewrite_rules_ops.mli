(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Sorts
open Univ
open Declarations
open Constr

module QGraph : sig
  type t
  val merge_qconstraints : Sorts.QConstraints.t -> t -> t * Sorts.QConstraints.t
  val to_qconstraints : t -> Sorts.QConstraints.t

  val to_pair : t -> Quality.t QVar.Map.t * QVar.Set.t
  val of_pair : 'a QVar.Map.t -> Quality.t QVar.Map.t * QVar.Set.t -> t
end

type eq_cmp = LEQ | EQ | GEQ

type extra_env = {
  evar_list: Evar.t list; (* Context style, later evars may depend on earlier ones *)
  evar_map : (rel_context * types * relevance * Names.Name.t) Evar.Map.t;
  qualities : bool QVar.Map.t;
  univs : bool Level.Map.t;
  evar_candidates : (eq_cmp * constr) list Evar.Map.t;
  equalities: (relevance Range.t * QVar.t * constr * Conversion.conv_pb * constr) list;
  qcstrs: QConstraints.t;
  ucstrs: (Quality.t * Universe.t * Conversion.conv_pb * Universe.t) list;
  qgraph : QGraph.t;
  ulcstrs: Constraints.t;
  pattern_relevances: QVar.Set.t;
}

module ExtraEnv : sig
  val empty : extra_env

  val add_quality :   QVar.t -> bound:bool -> extra_env -> extra_env
  val add_universe : Level.t -> bound:bool -> extra_env -> extra_env
  val add_evar : Evar.t -> rel_context -> types -> relevance -> Names.Name.t -> extra_env -> extra_env
  val add_pattern_relevance : relevance -> extra_env -> extra_env
  val enforce_constraints : extra_env -> Univ.Constraints.t -> extra_env

  val enforce_super_level : Sorts.t -> Level.t -> extra_env -> extra_env
  val enforce_product_level : Environ.env -> Sorts.t -> Sorts.t -> Level.t -> extra_env -> extra_env

  val sigma_of : extra_env -> Typeops.evar_handler
end

val reduce_to_prod :
  Environ.env -> extra_env -> (Evar.t * QVar.t * Level.t) * (Evar.t * QVar.t * Level.t) -> constr ->
  extra_env * (constr * relevance * constr)

val reduce_to_appind :
  Environ.env -> extra_env -> Names.inductive -> QVar.t array * Level.t array * Evar.t array -> constr ->
  extra_env * (UVars.Instance.t * constr array)

val instantiate : rel_context -> constr list -> Vars.substituend Esubst.subs -> Vars.substituend Esubst.subs

val cumul_lax : Environ.env -> extra_env -> types -> types -> extra_env

val unify_lax : relevance Range.t -> Conversion.conv_pb -> (imitation_cmp * constr) Evar.Map.t -> Environ.env ->
  extra_env -> constr -> constr -> extra_env


val judge_of_inductive : Environ.env -> extra_env -> pinductive -> extra_env * Environ.unsafe_judgment

val judge_of_constructor : Environ.env -> extra_env -> pconstructor -> extra_env * Environ.unsafe_judgment

val judge_of_constant : Environ.env -> extra_env -> pconstant -> extra_env * Environ.unsafe_judgment

val typecheck_pattern : Environ.env -> pattern -> extra_env * Environ.unsafe_judgment


val noccur_evar : Environ.env -> extra_env -> (imitation_cmp * constr) Evar.Map.t -> Evar.t -> constr -> bool

val add_evar_definition : Environ.env -> extra_env -> (imitation_cmp * constr) Evar.Map.t -> Evar.t -> imitation_cmp * constr -> extra_env * (imitation_cmp * constr) Evar.Map.t

val push_equality :
  Environ.env -> extra_env -> (imitation_cmp * constr) Evar.Map.t -> (relevance Range.t * QVar.t * constr * Conversion.conv_pb * constr) ->
  extra_env * bool

val push_uconstraint :
  QGraph.t -> (Quality.t * Universe.t * Conversion.conv_pb * Universe.t) -> Constraints.t -> Constraints.t

val evar_handler : CClosure.evar_handler

val check_inferred_constraints: Environ.env -> extra_env -> rewrite_rule_info -> unit

val check_pattern_relevances : extra_env -> relevance -> unit

val check_pattern_redex : Environ.env -> Declarations.pattern -> unit

val check_ucstr_slow : Environ.env -> rewrite_rule_info -> Sorts.t * conv_pb * Sorts.t -> bool

val imitate : Environ.env -> extra_env -> (imitation_cmp * types) Evar.Map.t ->
  (extra_env -> unit -> extra_env * Level.t) -> eq_cmp -> types -> (extra_env * (imitation_cmp * types)) option

val nf_evar : rewrite_rule_info -> constr -> constr

val nf_evar_map : Evar.t list -> QGraph.t -> (imitation_cmp * constr) Evar.Map.t ->
  (rel_context * types * relevance * Names.Name.t) Evar.Map.t ->
  (rel_context * types * relevance * Names.Name.t) Evar.Map.t

val nf_evar_info : rewrite_rule_info -> rewrite_rule_info

type pattern_translation_error =
  | UnknownEvar
  | UnknownQVar of Sorts.QVar.t
  | UnknownLevel of Univ.Level.t
  | DuplicatePatVar of Evar.t * Names.Id.t * int * int
  | DuplicateQVar of Sorts.QVar.t * int * int
  | DuplicateUVar of Univ.Level.t * int * int
  | NoHeadSymbol

exception PatternTranslationError of pattern_translation_error

val translate_rewrite_rule : Environ.env -> rewrite_rule -> Names.Constant.t * machine_rewrite_rule

val head_symbol : pattern -> Names.Constant.t
