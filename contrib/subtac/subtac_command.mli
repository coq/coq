open Pretyping
open Evd
open Environ
open Term
open Topconstr
open Names
open Libnames
open Pp
open Vernacexpr
open Constrintern

val interp_gen :
  typing_constraint ->
  evar_defs ref ->
  env ->
  ?impls:full_implicits_env ->
  ?allow_patvar:bool ->
  ?ltacvars:ltac_sign ->
  constr_expr -> constr
val interp_constr :
  evar_defs ref ->
  env -> constr_expr -> constr
val interp_type_evars :
  evar_defs ref ->
  env ->
  ?impls:full_implicits_env ->
  constr_expr -> constr
val interp_casted_constr_evars :
  evar_defs ref ->
  env ->
  ?impls:full_implicits_env ->
  constr_expr -> types -> constr
val interp_open_constr :
  evar_defs ref -> env -> constr_expr -> constr
val interp_constr_judgment :
  evar_defs ref ->
  env ->
  constr_expr -> unsafe_judgment
val list_chop_hd : int -> 'a list -> 'a list * 'a * 'a list

val interp_binder :     Evd.evar_defs ref ->
    Environ.env -> Names.name -> Topconstr.constr_expr -> Term.constr



val build_recursive :
  (fixpoint_expr * decl_notation) list -> bool -> unit

val build_corecursive :
  (cofixpoint_expr * decl_notation) list -> bool -> unit
