(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
open Environ
open Names

type state

type rigidity = Rigid | Freestanding

module State : sig
  val make : Evd.evar_map -> state
  val evar_map : state -> Evd.evar_map
  val sigma_of : state -> constr Evar.Map.t -> Evd.evar_map

  val add_patvar : ?loc:Loc.t -> name:Name.t -> env -> state -> types -> relevance -> rigidity -> state * (int * types)
  val add_quality: ?loc:Loc.t -> ?name:Id.t -> state -> state * (int quality_pattern * Quality.t)
  val add_level :  ?loc:Loc.t -> ?name:Id.t -> state -> state * (int * Level.t)

  val add_pattern_relevance : relevance -> state -> state

  val enforce_constraints : state -> PConstraints.t -> state

  val create_universe : ?loc:Loc.t -> state -> state * Sorts.t

  val create_super_sort : env -> state -> Sorts.t -> state * Sorts.t
  val create_product_sort : env -> state -> Sorts.t -> Sorts.t -> state * Sorts.t
end

val reduce_to_prod : env -> state -> types -> state * (types * relevance * types)
val reduce_to_appind : env -> state -> inductive -> types -> state * (UVars.Instance.t * types array)

val indtyping_helper :
  ('env -> state -> types * relevance -> 'preterm -> state * 'res) ->
  ('res -> types) ->
  (state -> rel_context -> 'env -> rel_context * 'env) ->
  ('env -> env) ->
  'env -> state -> unsafe_judgment -> inductive ->
  ?pnas:Name.t array -> ?pna:Name.t -> 'preterm -> (Name.t array option * 'preterm) array ->
  state
  * (case_info * UVars.Instance.t * types array * ('res, relevance) pcase_return
      * constr pcase_invert * types * ('res, relevance) pcase_branch array)
  * types

val instantiate : rel_context -> constr list -> Vars.substituend Esubst.subs -> Vars.substituend Esubst.subs

val cumul_lax : env -> state -> types -> types -> state

type names = {
  sort_names : Name.t array;
  level_names : Name.t array;
  evar_names : Name.t array;
}

val typecheck_finalize : loc:Loc.t option -> env -> state -> pattern -> unsafe_judgment -> names * (int Evar.Map.t * UVars.sort_level_subst) * Evd.evar_map * UnivConstraints.t QVar.Map.t * pattern * unsafe_judgment

val judge_of_inductive : env -> state -> pinductive -> state * unsafe_judgment

val judge_of_constructor : env -> state -> pconstructor -> state * unsafe_judgment

val judge_of_constant : env -> state -> pconstant -> state * unsafe_judgment

val typecheck_pattern : env -> names -> pattern -> state * unsafe_judgment

type pattern_translation_error =
  | UnknownEvar of Evar.t
  | UnknownQuality of Sorts.Quality.t
  | UnknownLevel of Univ.Level.t
  | NoHeadSymbol

exception LocalPatternTranslationError of pattern_translation_error

val translate_rewrite_rule : Environ.env -> Evd.evar_map -> rewrite_rule -> Names.Constant.t * machine_rewrite_rule

val head_symbol : pattern -> Names.Constant.t
