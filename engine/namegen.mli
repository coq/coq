(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Context
open Environ

(*********************************************************************
   Conventional default names *)

val default_prop_ident : Id.t          (* "H" *)
val default_small_ident : Id.t         (* "H" *)
val default_type_ident : Id.t          (* "X" *)
val default_non_dependent_ident : Id.t (* "H" *)
val default_dependent_ident : Id.t     (* "x" *)

(*********************************************************************
   Generating "intuitive" names from their type *)

val lowercase_first_char : Id.t -> string
val sort_hdchar : sorts -> string
val hdchar : env -> types -> string
val id_of_name_using_hdchar : env -> types -> Name.t -> Id.t
val named_hd : env -> types -> Name.t -> Name.t
val head_name : types -> Id.t option

val mkProd_name : env -> Name.t * types * types -> types
val mkLambda_name : env -> Name.t * types * constr -> constr

(** Deprecated synonyms of [mkProd_name] and [mkLambda_name] *)
val prod_name : env -> Name.t * types * types -> types
val lambda_name : env -> Name.t * types * constr -> constr

val prod_create : env -> types * types -> constr
val lambda_create : env -> types * constr -> constr
val name_assumption : env -> rel_declaration -> rel_declaration
val name_context : env -> rel_context -> rel_context

val mkProd_or_LetIn_name : env -> types -> rel_declaration -> types
val mkLambda_or_LetIn_name : env -> constr -> rel_declaration -> constr
val it_mkProd_or_LetIn_name   : env -> types -> rel_context -> types
val it_mkLambda_or_LetIn_name : env -> constr -> rel_context -> constr

(*********************************************************************
   Fresh names *)

(** Avoid clashing with a name satisfying some predicate *)
val next_ident_away_from : Id.t -> (Id.t -> bool) -> Id.t

(** Avoid clashing with a name of the given list *)
val next_ident_away : Id.t -> Id.t list -> Id.t

(** Avoid clashing with a name already used in current module *)
val next_ident_away_in_goal : Id.t -> Id.t list -> Id.t

(** Avoid clashing with a name already used in current module 
   but tolerate overwriting section variables, as in goals *)
val next_global_ident_away : Id.t -> Id.t list -> Id.t

(** Avoid clashing with a constructor name already used in current module *)
val next_name_away_in_cases_pattern : (Termops.names_context * constr) -> Name.t -> Id.t list -> Id.t

(** Default is [default_non_dependent_ident] *)
val next_name_away  : Name.t -> Id.t list -> Id.t

val next_name_away_with_default : string -> Name.t -> Id.t list ->
  Id.t

val next_name_away_with_default_using_types : string -> Name.t ->
  Id.t list -> types -> Id.t

val set_reserved_typed_name : (types -> Name.t) -> unit

(*********************************************************************
   Making name distinct for displaying *)

type renaming_flags =
  | RenamingForCasesPattern of (Name.t list * constr) (** avoid only global constructors *)
  | RenamingForGoal (** avoid all globals (as in intro) *)
  | RenamingElsewhereFor of (Name.t list * constr)

val make_all_name_different : env -> env

val compute_displayed_name_in :
  renaming_flags -> Id.t list -> Name.t -> constr -> Name.t * Id.t list
val compute_and_force_displayed_name_in :
  renaming_flags -> Id.t list -> Name.t -> constr -> Name.t * Id.t list
val compute_displayed_let_name_in :
  renaming_flags -> Id.t list -> Name.t -> constr -> Name.t * Id.t list
val rename_bound_vars_as_displayed :
  Id.t list -> Name.t list -> types -> types

(**********************************************************************)
(* Naming strategy for arguments in Prop when eliminating inductive types *)

val use_h_based_elimination_names : unit -> bool
