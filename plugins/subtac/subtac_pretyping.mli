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

val interp :
    Environ.env ->
    Evd.evar_map ref ->
    Rawterm.glob_constr ->
    Evarutil.type_constraint -> Term.constr * Term.constr

val subtac_process : ?is_type:bool -> env -> evar_map ref -> identifier -> local_binder list ->
  constr_expr -> constr_expr option -> evar_map * constr * types * manual_explicitation list

val subtac_proof : Decl_kinds.definition_kind -> Tacexpr.declaration_hook -> env -> evar_map ref -> identifier -> local_binder list ->
  constr_expr -> constr_expr option -> Subtac_obligations.progress
