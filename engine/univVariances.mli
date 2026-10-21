(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val universe_variances : Environ.env -> Evd.evar_map -> ?typ:EConstr.t -> EConstr.t -> InferCumulativity.variances
val universe_variances_constr : Environ.env -> Evd.evar_map -> ?typ:Constr.t -> Constr.t -> InferCumulativity.variances

val register_universe_variances_of_constr : Environ.env -> Evd.evar_map -> ?typ:Constr.t -> Constr.t -> Evd.evar_map

val register_universe_variances_of : Environ.env -> Evd.evar_map -> ?typ:EConstr.t -> EConstr.t -> Evd.evar_map

val register_universe_variances_of_undefined : Environ.env -> Evd.evar_map -> Evd.evar_map

val register_universe_variances_of_type : Environ.env -> Evd.evar_map -> EConstr.t -> Evd.evar_map

val register_universe_variances_of_inductive : Environ.env -> Evd.evar_map ->
  udecl:UState.universe_decl ->
  cumulative:bool ->
  params:EConstr.rel_context ->
  arities:EConstr.t list ->
  constructors:(Names.Id.t list * EConstr.t list) list -> Evd.evar_map

val register_universe_variances_of_record : Environ.env -> Evd.evar_map -> env_ar_pars:Environ.env ->
  params:EConstr.rel_context ->
  fields:EConstr.rel_context list ->
  types:EConstr.t list -> Evd.evar_map

val register_universe_variances_of_fix :
  Environ.env -> Evd.evar_map ->
  EConstr.t list ->
  EConstr.t option list ->
  Evd.evar_map

val register_universe_variances_of_proofs :
  Environ.env -> Evd.evar_map ->
  (Constr.t * Constr.t) list ->
  Evd.evar_map

val register_universe_variances_of_eproofs :
  Environ.env -> Evd.evar_map ->
  (EConstr.t * EConstr.t) list ->
  Evd.evar_map

val register_universe_variances_of_proof_statements :
  Environ.env -> Evd.evar_map ->
  EConstr.t list ->
  Evd.evar_map

val register_universe_variances_of_partial_proofs :
  Environ.env -> Evd.evar_map ->
  EConstr.t list ->
  Evd.evar_map

val register_universe_variances_of_named_context :
  Environ.env -> Evd.evar_map ->
  as_types:bool ->
  ?cumul_pb:InferCumulativity.cumul_pb ->
  (* The variance with which to analyze each binding in the context *)
  EConstr.named_context ->
  Evd.evar_map
