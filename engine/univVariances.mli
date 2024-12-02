(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val universe_variances : Environ.env -> Evd.evar_map -> ?typ:EConstr.t -> EConstr.t -> UnivMinim.level_variances

val universe_variances_of_type : Environ.env -> Evd.evar_map -> EConstr.t -> UnivMinim.level_variances

val universe_variances_of_inductive : Environ.env -> Evd.evar_map ->
  params:EConstr.rel_context ->
  arities:EConstr.t list ->
  constructors:(Names.Id.t list * EConstr.t list) list -> UnivMinim.level_variances

val universe_variances_of_record : Environ.env -> Evd.evar_map ->
  params:EConstr.rel_context ->
  fields:EConstr.rel_context list ->
  types:EConstr.t list -> UnivMinim.level_variances

val universe_variances_of_proofs :
  Environ.env -> Evd.evar_map ->
  (Constr.t * Constr.t) list ->
  UnivMinim.level_variances

val universe_variances_of_named_context :
  Environ.env -> Evd.evar_map ->
  ?variance:UVars.Variance.t ->
  (* The variance with which to analyze each binding in the context *)
  EConstr.named_context ->
  UnivMinim.level_variances
