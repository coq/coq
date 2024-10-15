(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Evd
open Environ
open Libnames
open Glob_term
open Pattern
open EConstr
open Constrexpr
open Notation_term
open Pretyping

(** Translation from front abstract syntax of term to untyped terms (glob_constr) *)

(** The translation performs:

   - resolution of names :
      - check all variables are bound
      - make absolute the references to global objets
   - resolution of symbolic notations using scopes
   - insertion of implicit arguments

   To interpret implicit arguments and arg scopes of recursive variables
   while internalizing inductive types and recursive definitions, and also
   projection while typing records.

   the third and fourth arguments associate a list of implicit
   positions and scopes to identifiers declared in the [rel_context]
   of [env] *)

type var_internalization_type =
  | Inductive
  | Recursive
  | Method
  | Variable

(** This collects relevant information for interning local variables:
   - their coqdoc kind (a recursive call in a inductive, fixpoint of class; or a bound variable)
     e.g. while typing the constructor of JMeq, "JMeq" behaves as a variable of type Inductive
   - their implicit arguments
   - their argument scopes *)
type var_internalization_data

(** A map of free variables to their implicit arguments and scopes *)
type internalization_env = var_internalization_data Id.Map.t

val empty_internalization_env : internalization_env

val compute_internalization_data : env -> evar_map -> ?silent:bool -> Id.t -> var_internalization_type ->
  types -> Impargs.manual_implicits -> var_internalization_data

val compute_internalization_env : env -> evar_map -> ?impls:internalization_env -> ?force:Id.Set.t list -> var_internalization_type ->
  Id.t list -> types list -> Impargs.manual_implicits list ->
  internalization_env

val implicits_of_decl_in_internalization_env :
  Id.t -> internalization_env -> Impargs.implicit_status list

type ltac_sign = {
  ltac_vars : Id.Set.t;
  (** Variables of Ltac which may be bound to a term *)
  ltac_bound : Id.Set.t;
  (** Other variables of Ltac *)
  ltac_extra : Genintern.Store.t;
  (** Arbitrary payload *)
}

val empty_ltac_sign : ltac_sign

(** {6 Internalization performs interpretation of global names and notations } *)

val intern_constr : env -> evar_map -> constr_expr -> glob_constr
val intern_type : env -> evar_map -> constr_expr -> glob_constr

val intern_gen : typing_constraint -> env -> evar_map ->
  ?impls:internalization_env -> ?strict_check:bool -> ?pattern_mode:bool -> ?ltacvars:ltac_sign ->
  constr_expr -> glob_constr

val intern_unknown_if_term_or_type : env -> evar_map -> constr_expr -> glob_constr

val intern_pattern : env -> cases_pattern_expr ->
  lident list * (Id.t Id.Map.t * cases_pattern) list

val intern_context : env -> bound_univs:UnivNames.universe_binders ->
  internalization_env -> local_binder_expr list -> internalization_env * glob_decl list

(** {6 Composing internalization with type inference (pretyping) } *)

(** Main interpretation functions, using type class inference,
    expecting evars and pending problems to be all resolved *)

val interp_constr : ?flags:inference_flags -> ?expected_type:typing_constraint -> env -> evar_map -> ?impls:internalization_env ->
  constr_expr -> constr Evd.in_ustate

val interp_casted_constr : ?flags:inference_flags -> env -> evar_map -> ?impls:internalization_env ->
  constr_expr -> types -> constr Evd.in_ustate

val interp_type : ?flags:inference_flags -> env -> evar_map -> ?impls:internalization_env ->
  constr_expr -> types Evd.in_ustate

(** Main interpretation function expecting all postponed problems to
    be resolved, but possibly leaving evars. *)

val interp_open_constr : ?expected_type:typing_constraint -> env -> evar_map -> constr_expr -> evar_map * constr

(** Accepting unresolved evars *)

val interp_constr_evars : ?program_mode:bool -> env -> evar_map ->
  ?impls:internalization_env -> constr_expr -> evar_map * constr

val interp_casted_constr_evars : ?program_mode:bool -> env -> evar_map ->
  ?impls:internalization_env -> constr_expr -> types -> evar_map * constr

val interp_type_evars : ?program_mode:bool -> env -> evar_map ->
  ?impls:internalization_env -> constr_expr -> evar_map * types

(** Accepting unresolved evars and giving back the manual implicit arguments *)

val interp_constr_evars_impls : ?program_mode:bool -> env -> evar_map ->
  ?impls:internalization_env -> constr_expr ->
  evar_map * (constr * Impargs.manual_implicits)

val interp_casted_constr_evars_impls : ?program_mode:bool -> env -> evar_map ->
  ?impls:internalization_env -> constr_expr -> types ->
  evar_map * (constr * Impargs.manual_implicits)

val interp_type_evars_impls : ?flags:inference_flags -> env -> evar_map ->
  ?impls:internalization_env -> constr_expr ->
  evar_map * (types * Impargs.manual_implicits)

(** Interprets constr patterns *)

(** Without typing *)
val intern_constr_pattern :
  env -> evar_map -> ?as_type:bool -> ?strict_check:bool -> ?ltacvars:ltac_sign ->
    constr_pattern_expr -> Id.Set.t * constr_pattern

val intern_uninstantiated_constr_pattern :
  env -> evar_map -> ?as_type:bool -> ?strict_check:bool -> ?ltacvars:ltac_sign ->
    constr_pattern_expr -> Id.Set.t * [`uninstantiated] constr_pattern_r

(** Returns None if it's an abbreviation not bound to a name, raises an error
    if not existing *)
val intern_reference : qualid -> GlobRef.t option

(** Returns None if not a reference or a abbrev not bound to a name *)
val intern_name_alias :
  constr_expr -> (GlobRef.t * Glob_term.glob_instance option) option

(** Expands abbreviations; raise an error if not existing *)
val interp_reference : ltac_sign -> qualid -> glob_constr

(** Interpret binders *)

val interp_binder  : env -> evar_map -> Name.t -> constr_expr ->
  types Evd.in_ustate

val interp_binder_evars : env -> evar_map -> Name.t -> constr_expr -> evar_map * types

(** Interpret contexts: returns extended env and context. *)

val interp_context_evars :
  ?program_mode:bool -> ?unconstrained_sorts:bool -> ?impl_env:internalization_env ->
  env -> evar_map -> local_binder_expr list ->
  evar_map * (internalization_env * ((env * rel_context) * Impargs.manual_implicits))

(** Interpret named contexts *)

val interp_named_context_evars :
  ?program_mode:bool -> ?unconstrained_sorts:bool -> ?impl_env:internalization_env -> ?autoimp_enable:bool ->
  env -> evar_map -> local_binder_expr list ->
  evar_map * (internalization_env * ((env * named_context) * Impargs.manual_implicits))

(** Locating references of constructions, possibly via a syntactic definition
   (these functions do not modify the glob file) *)

val locate_reference :  Libnames.qualid -> GlobRef.t option
val is_global : Id.t -> bool

(** Interprets a term as the left-hand side of a notation. The returned map is
    guaranteed to have the same domain as the input one. *)
val interp_notation_constr : env -> ?impls:internalization_env ->
  notation_interp_env -> constr_expr ->
  (bool * subscopes * Id.Set.t) Id.Map.t * notation_constr * reversibility_status

(** Idem but to glob_constr (weaker check of binders) *)

val intern_core : typing_constraint ->
  env -> evar_map -> ?strict_check:bool -> ?pattern_mode:bool -> ?ltacvars:ltac_sign ->
  Genintern.intern_variable_status -> constr_expr ->
  glob_constr

(** Globalization options *)
val parsing_explicit : bool ref

(** Placeholder for global option, should be moved to a parameter *)
val get_asymmetric_patterns : unit -> bool

val check_duplicate : ?loc:Loc.t -> (qualid * constr_expr) list -> unit
(** Check that a list of record field definitions doesn't contain
    duplicates. *)

val interp_univ_constraint
  : Evd.evar_map
  -> sort_name_expr * Univ.constraint_type * sort_name_expr
  -> Univ.univ_constraint

(** Local universe and constraint declarations. *)
val interp_univ_decl : Environ.env -> universe_decl_expr ->
                       Evd.evar_map * UState.universe_decl

val interp_univ_decl_opt : Environ.env -> universe_decl_expr option ->
                       Evd.evar_map * UState.universe_decl

val interp_cumul_univ_decl_opt : Environ.env -> cumul_univ_decl_expr option ->
  Evd.evar_map * UState.universe_decl * Entries.variance_entry
(** BEWARE the variance entry needs to be adjusted by
   [ComInductive.variance_of_entry] if the instance is extensible. *)

val interp_mutual_univ_decl_opt : Environ.env -> universe_decl_expr option list ->
  Evd.evar_map * UState.universe_decl
(** Check that all defined udecls of a list of udecls associated to a mutual definition
    are the same and interpret this common udecl *)
