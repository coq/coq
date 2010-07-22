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
  evar_map ref ->
  env ->
  ?impls:internalization_env ->
  ?allow_patvar:bool ->
  ?ltacvars:ltac_sign ->
  constr_expr -> constr
val interp_constr :
  evar_map ref ->
  env -> constr_expr -> constr
val interp_type_evars :
  evar_map ref ->
  env ->
  ?impls:internalization_env ->
  constr_expr -> constr
val interp_casted_constr_evars :
  evar_map ref ->
  env ->
  ?impls:internalization_env ->
  constr_expr -> types -> constr
val interp_open_constr :
  evar_map ref -> env -> constr_expr -> constr
val interp_constr_judgment :
  evar_map ref ->
  env ->
  constr_expr -> unsafe_judgment
val list_chop_hd : int -> 'a list -> 'a list * 'a * 'a list

val interp_binder :     Evd.evar_map ref ->
    Environ.env -> Names.name -> Topconstr.constr_expr -> Term.constr


val telescope :
  (Names.name * 'a option * Term.types) list ->
  Term.types * (Names.name * Term.types option * Term.types) list *
    Term.constr

val build_wellfounded :
           Names.identifier * 'a * Topconstr.local_binder list *
           Topconstr.constr_expr * Topconstr.constr_expr ->
           Topconstr.constr_expr ->
           Topconstr.constr_expr -> 'b -> 'c -> Subtac_obligations.progress

val build_recursive :
  (fixpoint_expr * decl_notation list) list -> bool -> unit

val build_corecursive :
  (cofixpoint_expr * decl_notation list) list -> bool -> unit
