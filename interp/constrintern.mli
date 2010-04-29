(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

(*i $Id$ i*)

open Names
open Term
open Sign
open Evd
open Environ
open Libnames
open Rawterm
open Pattern
open Topconstr
open Termops
open Pretyping

(** {6 Sect } *)
(** Translation from front abstract syntax of term to untyped terms (rawconstr)

   The translation performs:

   - resolution of names :
      - check all variables are bound
      - make absolute the references to global objets
   - resolution of symbolic notations using scopes
   - insert existential variables for implicit arguments
*)

(** To interpret implicits and arg scopes of recursive variables while
   internalizing inductive types and recursive definitions, and also
   projection while typing records.

   the third and fourth arguments associate a list of implicit
   positions and scopes to identifiers declared in the [rel_context]
   of [env] *)

type var_internalization_type = Inductive | Recursive | Method

type var_internalization_data =
    var_internalization_type *
    identifier list *
    Impargs.implicits_list *
    scope_name option list

(** A map of free variables to their implicit arguments and scopes *)
type internalization_env =
    (identifier * var_internalization_data) list

(** Contains also a list of identifiers to automatically apply to the variables*)
type full_internalization_env =
    identifier list * internalization_env

val empty_internalization_env : full_internalization_env

val compute_internalization_data : env -> var_internalization_type ->
  types -> Impargs.manual_explicitation list -> var_internalization_data

val set_internalization_env_params :
  internalization_env -> identifier list -> full_internalization_env

val compute_full_internalization_env : env ->
  var_internalization_type ->
  identifier list -> identifier list -> types list ->
  Impargs.manual_explicitation list list -> full_internalization_env

type manual_implicits = (explicitation * (bool * bool * bool)) list

type ltac_sign = identifier list * unbound_ltac_var_map

type raw_binder = (name * binding_kind * rawconstr option * rawconstr)

(** {6 Internalisation performs interpretation of global names and notations } *)

val intern_constr : evar_map -> env -> constr_expr -> rawconstr

val intern_type : evar_map -> env -> constr_expr -> rawconstr

val intern_gen : bool -> evar_map -> env ->
  ?impls:full_internalization_env -> ?allow_patvar:bool -> ?ltacvars:ltac_sign ->
  constr_expr -> rawconstr

val intern_pattern : env -> cases_pattern_expr ->
  Names.identifier list *
    ((Names.identifier * Names.identifier) list * Rawterm.cases_pattern) list

val intern_context : bool -> evar_map -> env -> local_binder list -> raw_binder list

(** {6 Composing internalization with pretyping } *)

(** Main interpretation function *)

val interp_gen : typing_constraint -> evar_map -> env ->
  ?impls:full_internalization_env -> ?allow_patvar:bool -> ?ltacvars:ltac_sign ->
  constr_expr -> constr

(** Particular instances *)

val interp_constr : evar_map -> env ->
  constr_expr -> constr

val interp_type : evar_map -> env -> ?impls:full_internalization_env ->
  constr_expr -> types

val interp_open_constr   : evar_map -> env -> constr_expr -> evar_map * constr

val interp_open_constr_patvar   : evar_map -> env -> constr_expr -> evar_map * constr

val interp_casted_constr : evar_map -> env -> ?impls:full_internalization_env ->
  constr_expr -> types -> constr

(** Accepting evars and giving back the manual implicits in addition. *)

val interp_casted_constr_evars_impls : ?evdref:(evar_map ref) -> ?fail_evar:bool -> env ->
  ?impls:full_internalization_env -> constr_expr -> types -> constr * manual_implicits

val interp_type_evars_impls : ?evdref:(evar_map ref) -> ?fail_evar:bool ->
  env -> ?impls:full_internalization_env ->
  constr_expr -> types * manual_implicits

val interp_constr_evars_impls : ?evdref:(evar_map ref) -> ?fail_evar:bool ->
  env -> ?impls:full_internalization_env ->
  constr_expr -> constr * manual_implicits

val interp_casted_constr_evars : evar_map ref -> env ->
  ?impls:full_internalization_env -> constr_expr -> types -> constr

val interp_type_evars : evar_map ref -> env -> ?impls:full_internalization_env ->
  constr_expr -> types

(** {6 Build a judgment  } *)

val interp_constr_judgment : evar_map -> env -> constr_expr -> unsafe_judgment

(** Interprets constr patterns *)

val intern_constr_pattern :
  evar_map -> env -> ?as_type:bool -> ?ltacvars:ltac_sign ->
    constr_pattern_expr -> patvar list * constr_pattern

(** Raise Not_found if syndef not bound to a name and error if unexisting ref *)
val intern_reference : reference -> global_reference

(** Expands abbreviations (syndef); raise an error if not existing *)
val interp_reference : ltac_sign -> reference -> rawconstr

(** Interpret binders *)

val interp_binder  : evar_map -> env -> name -> constr_expr -> types

val interp_binder_evars : evar_map ref -> env -> name -> constr_expr -> types

(** Interpret contexts: returns extended env and context *)

val interp_context_gen : (env -> rawconstr -> types) ->
  (env -> rawconstr -> unsafe_judgment) ->
  ?fail_anonymous:bool ->
  evar_map -> env -> local_binder list -> (env * rel_context) * manual_implicits
  
val interp_context : ?fail_anonymous:bool ->
  evar_map -> env -> local_binder list -> (env * rel_context) * manual_implicits

val interp_context_evars : ?fail_anonymous:bool ->
  evar_map ref -> env -> local_binder list -> (env * rel_context) * manual_implicits

(** Locating references of constructions, possibly via a syntactic definition 
   (these functions do not modify the glob file) *)

val is_global : identifier -> bool
val construct_reference : named_context -> identifier -> constr
val global_reference : identifier -> constr
val global_reference_in_absolute_module : dir_path -> identifier -> constr

(** Interprets into a abbreviatable constr *)

val interp_aconstr : ?impls:full_internalization_env ->
  identifier list * identifier list -> constr_expr -> interpretation

(** Globalization leak for Grammar *)
val for_grammar : ('a -> 'b) -> 'a -> 'b
