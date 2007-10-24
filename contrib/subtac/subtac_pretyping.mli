open Term
open Environ
open Names
open Sign
open Evd
open Global
open Topconstr

module Pretyping : Pretyping.S

val subtac_process : env -> evar_defs ref -> identifier -> local_binder list ->
  constr_expr -> constr_expr option -> evar_map * constr * types

val subtac_proof : env -> evar_defs ref -> identifier -> local_binder list ->
  constr_expr -> constr_expr option -> Subtac_obligations.progress
