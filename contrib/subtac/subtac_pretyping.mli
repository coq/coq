open Term
open Environ
open Names
open Sign
open Evd
open Global
open Topconstr
open Implicit_quantifiers
open Impargs

module Pretyping : Pretyping.S

val subtac_process : env -> evar_defs ref -> identifier -> typeclass_context -> local_binder list ->
  constr_expr -> constr_expr option -> evar_map * constr * types * manual_explicitation list

val subtac_proof : env -> evar_defs ref -> identifier -> typeclass_context -> local_binder list ->
  constr_expr -> constr_expr option -> Subtac_obligations.progress
