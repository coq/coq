(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Environ

(*********************************************************************
   Generating "intuitive" names from their type *)

val lowercase_first_char : identifier -> string
val sort_hdchar : sorts -> string
val hdchar : env -> types -> string
val id_of_name_using_hdchar : env -> types -> name -> identifier
val named_hd : env -> types -> name -> name

val mkProd_name : env -> name * types * types -> types
val mkLambda_name : env -> name * types * constr -> constr

(** Deprecated synonyms of [mkProd_name] and [mkLambda_name] *)
val prod_name : env -> name * types * types -> types
val lambda_name : env -> name * types * constr -> constr

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

(** Avoid clashing with a name of the given list *)
val next_ident_away : identifier -> identifier list -> identifier

(** Avoid clashing with a name already used in current module *)
val next_ident_away_in_goal : identifier -> identifier list -> identifier

(** Avoid clashing with a name already used in current module 
   but tolerate overwriting section variables, as in goals *)
val next_global_ident_away : identifier -> identifier list -> identifier

(** Avoid clashing with a constructor name already used in current module *)
val next_name_away_in_cases_pattern : name -> identifier list -> identifier

val next_name_away  : name -> identifier list -> identifier (** default is "H" *)
val next_name_away_with_default : string -> name -> identifier list ->
  identifier

(*********************************************************************
   Making name distinct for displaying *)

type renaming_flags =
  | RenamingForCasesPattern (** avoid only global constructors *)
  | RenamingForGoal (** avoid all globals (as in intro) *)
  | RenamingElsewhereFor of constr

val make_all_name_different : env -> env

val compute_displayed_name_in :
  renaming_flags -> identifier list -> name -> constr -> name * identifier list
val compute_and_force_displayed_name_in :
  renaming_flags -> identifier list -> name -> constr -> name * identifier list
val compute_displayed_let_name_in :
  renaming_flags -> identifier list -> name -> constr -> name * identifier list
val rename_bound_vars_as_displayed : identifier list -> types -> types
