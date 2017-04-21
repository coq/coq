(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Evd
open Environ
open Libnames
open Globnames
open Glob_term
open Pattern
open Constrexpr
open Notation_term
open Pretyping
open Misctypes

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
  | Inductive of Id.t list (* list of params *)
  | Recursive
  | Method
  | Variable

type var_internalization_data =
    var_internalization_type *
      (** type of the "free" variable, for coqdoc, e.g. while typing the
	  constructor of JMeq, "JMeq" behaves as a variable of type Inductive *)
    Id.t list *
      (** impargs to automatically add to the variable, e.g. for "JMeq A a B b"
          in implicit mode, this is [A;B] and this adds (A:=A) and (B:=B) *)
    Impargs.implicit_status list * (** signature of impargs of the variable *)
    Notation_term.scope_name option list (** subscopes of the args of the variable *)

(** A map of free variables to their implicit arguments and scopes *)
type internalization_env = var_internalization_data Id.Map.t

val empty_internalization_env : internalization_env

val compute_internalization_data : env -> var_internalization_type ->
  types -> Impargs.manual_explicitation list -> var_internalization_data

val compute_internalization_env : env -> var_internalization_type ->
  Id.t list -> types list -> Impargs.manual_explicitation list list ->
  internalization_env

type ltac_sign = {
  ltac_vars : Id.Set.t;
  (** Variables of Ltac which may be bound to a term *)
  ltac_bound : Id.Set.t;
  (** Other variables of Ltac *)
}

val empty_ltac_sign : ltac_sign

(** {6 Internalization performs interpretation of global names and notations } *)

val intern_constr : env -> constr_expr -> glob_constr

val intern_type : env -> constr_expr -> glob_constr

val intern_gen : typing_constraint -> env ->
  ?impls:internalization_env -> ?allow_patvar:bool -> ?ltacvars:ltac_sign ->
  constr_expr -> glob_constr

val intern_pattern : env -> cases_pattern_expr ->
  Id.t list * (Id.t Id.Map.t * cases_pattern) list

val intern_context : bool -> env -> internalization_env -> local_binder_expr list -> internalization_env * glob_decl list

(** {6 Composing internalization with type inference (pretyping) } *)

(** Main interpretation functions, using type class inference,
    expecting evars and pending problems to be all resolved *)

val interp_constr : env -> evar_map -> ?impls:internalization_env ->
  constr_expr -> constr Evd.in_evar_universe_context

val interp_casted_constr : env -> evar_map -> ?impls:internalization_env ->
  constr_expr -> EConstr.types -> constr Evd.in_evar_universe_context

val interp_type : env -> evar_map -> ?impls:internalization_env ->
  constr_expr -> types Evd.in_evar_universe_context

(** Main interpretation function expecting all postponed problems to
    be resolved, but possibly leaving evars. *)

val interp_open_constr : env -> evar_map -> constr_expr -> evar_map * EConstr.constr

(** Accepting unresolved evars *)

val interp_constr_evars : env -> evar_map ref ->
  ?impls:internalization_env -> constr_expr -> EConstr.constr

val interp_casted_constr_evars : env -> evar_map ref ->
  ?impls:internalization_env -> constr_expr -> types -> EConstr.constr

val interp_type_evars : env -> evar_map ref ->
  ?impls:internalization_env -> constr_expr -> EConstr.types

(** Accepting unresolved evars and giving back the manual implicit arguments *)

val interp_constr_evars_impls : env -> evar_map ref ->
  ?impls:internalization_env -> constr_expr ->
  EConstr.constr * Impargs.manual_implicits

val interp_casted_constr_evars_impls : env -> evar_map ref ->
  ?impls:internalization_env -> constr_expr -> EConstr.types ->
  EConstr.constr * Impargs.manual_implicits

val interp_type_evars_impls : env -> evar_map ref ->
  ?impls:internalization_env -> constr_expr ->
  EConstr.types * Impargs.manual_implicits

(** Interprets constr patterns *)

val intern_constr_pattern :
  env -> ?as_type:bool -> ?ltacvars:ltac_sign ->
    constr_pattern_expr -> patvar list * constr_pattern

(** Raise Not_found if syndef not bound to a name and error if unexisting ref *)
val intern_reference : reference -> global_reference

(** Expands abbreviations (syndef); raise an error if not existing *)
val interp_reference : ltac_sign -> reference -> glob_constr

(** Interpret binders *)

val interp_binder  : env -> evar_map -> Name.t -> constr_expr -> 
  types Evd.in_evar_universe_context

val interp_binder_evars : env -> evar_map ref -> Name.t -> constr_expr -> EConstr.types

(** Interpret contexts: returns extended env and context *)

val interp_context_evars :
  ?global_level:bool -> ?impl_env:internalization_env -> ?shift:int ->
  env -> evar_map ref -> local_binder_expr list ->
  internalization_env * ((env * EConstr.rel_context) * Impargs.manual_implicits)

(* val interp_context_gen : (env -> glob_constr -> unsafe_type_judgment Evd.in_evar_universe_context) -> *)
(*   (env -> Evarutil.type_constraint -> glob_constr -> unsafe_judgment Evd.in_evar_universe_context) -> *)
(*   ?global_level:bool -> ?impl_env:internalization_env -> *)
(*   env -> evar_map -> local_binder_expr list -> internalization_env * ((env * Evd.evar_universe_context * rel_context * sorts list) * Impargs.manual_implicits) *)
  
(* val interp_context : ?global_level:bool -> ?impl_env:internalization_env -> *)
(*   env -> evar_map -> local_binder_expr list ->  *)
(*   internalization_env *  *)
(*   ((env * Evd.evar_universe_context * rel_context * sorts list) * Impargs.manual_implicits) *)

(** Locating references of constructions, possibly via a syntactic definition 
   (these functions do not modify the glob file) *)

val locate_reference :  Libnames.qualid -> Globnames.global_reference
val is_global : Id.t -> bool
val construct_reference : ('c, 't) Context.Named.pt -> Id.t -> constr
val global_reference : Id.t -> constr
val global_reference_in_absolute_module : DirPath.t -> Id.t -> constr

(** Interprets a term as the left-hand side of a notation. The returned map is
    guaranteed to have the same domain as the input one. *)
val interp_notation_constr : ?impls:internalization_env ->
  notation_interp_env -> constr_expr ->
  (bool * subscopes * notation_var_internalization_type) Id.Map.t *
  notation_constr * reversibility_flag

(** Globalization options *)
val parsing_explicit : bool ref

(** Globalization leak for Grammar *)
val for_grammar : ('a -> 'b) -> 'a -> 'b
