(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file features facilities to generate fresh names. *)

open Names
open Environ
open Evd
open EConstr

(** General evar naming using intro patterns  *)
type intro_pattern_naming_expr =
  | IntroIdentifier of Id.t
  | IntroFresh of Id.t
  | IntroAnonymous

(** Equalities on [intro_pattern_naming] *)
val intro_pattern_naming_eq :
  intro_pattern_naming_expr -> intro_pattern_naming_expr -> bool

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
val sort_hdchar : Sorts.t -> string
val hdchar : env -> evar_map -> types -> string
val id_of_name_using_hdchar : env -> evar_map -> types -> Name.t -> Id.t
val named_hd : env -> evar_map -> types -> Name.t -> Name.t
val head_name : evar_map -> types -> Id.t option

val mkProd_name : env -> evar_map -> Name.t EConstr.binder_annot * types * types -> types
val mkLambda_name : env -> evar_map -> Name.t EConstr.binder_annot * types * constr -> constr

(** Deprecated synonyms of [mkProd_name] and [mkLambda_name] *)
val prod_name : env -> evar_map -> Name.t EConstr.binder_annot * types * types -> types
val lambda_name : env -> evar_map -> Name.t EConstr.binder_annot * types * constr -> constr

val prod_create : env -> evar_map -> ERelevance.t * types * types -> constr
val lambda_create : env -> evar_map -> ERelevance.t * types * constr -> constr
val name_assumption : env -> evar_map -> rel_declaration -> rel_declaration
val name_context : env -> evar_map -> rel_context -> rel_context

val mkProd_or_LetIn_name : env -> evar_map -> types -> rel_declaration -> types
val mkLambda_or_LetIn_name : env -> evar_map -> constr -> rel_declaration -> constr
val it_mkProd_or_LetIn_name   : env -> evar_map -> types -> rel_context -> types
val it_mkLambda_or_LetIn_name : env -> evar_map -> constr -> rel_context -> constr

(*********************************************************************
   Fresh names *)

(** Avoid clashing with a name satisfying some predicate *)
val next_ident_away_from : Id.t -> (Id.t -> bool) -> Id.t

(** [next_ident_away original_id unwanted_ids] returns a new identifier as close as possible
    to the [original_id] while avoiding all [unwanted_ids].

    In particular:
    {ul {- if [original_id] does not appear in the list of [unwanted_ids], then [original_id] is returned.}
        {- if [original_id] appears in the list of [unwanted_ids],
           then this function returns a new id that:
           {ul {- has the same {i root} as the [original_id],}
               {- does not occur in the list of [unwanted_ids],}
               {- has the smallest possible {i subscript}.}}}}

    where by {i subscript} of some identifier we mean last part of it that is composed
    only from (decimal) digits and by {i root} of some identifier we mean
    the whole identifier except for the {i subscript}.

    E.g. if we take [foo42], then [42] is the {i subscript}, and [foo] is the root. *)
val next_ident_away : Id.t -> Id.Set.t -> Id.t

(** Avoid clashing with a name already used in current module *)
val next_ident_away_in_goal : Environ.env -> Id.t -> Id.Set.t -> Id.t

(** Avoid clashing with a name already used in current module
   but tolerate overwriting section variables, as in goals *)
val next_global_ident_away : Id.t -> Id.Set.t -> Id.t

(** Default is [default_non_dependent_ident] *)
val next_name_away  : Name.t -> Id.Set.t -> Id.t

val next_name_away_with_default : string -> Name.t -> Id.Set.t -> Id.t

val next_name_away_with_default_using_types : string -> Name.t ->
  Id.Set.t -> types -> Id.t

val set_reserved_typed_name : (types -> Name.t) -> unit

(*********************************************************************
   Making name distinct for displaying *)

val make_all_rel_context_name_different : env -> evar_map -> rel_context -> env * rel_context
val make_all_name_different : env -> evar_map -> env

module Generator :
sig
type 'a t
type 'a input = 'a t * 'a
val fresh : Nameops.Fresh.t t
val idset : Id.Set.t t

val next_name_away : 'a t -> Name.t -> 'a -> Id.t * 'a

val max_map : 'a t -> 'a -> Nameops.Subscript.t Id.Map.t
end

type renaming_flags =
  | RenamingForCasesPattern of (Name.t list * constr) (** avoid only global constructors *)
  | RenamingForGoal (** avoid all globals (as in intro) *)
  | RenamingElsewhereFor of (Name.t list * constr)

val compute_displayed_name_in :
  'a Generator.t -> Environ.env -> evar_map -> renaming_flags -> 'a -> Name.t -> constr -> Name.t * 'a
val compute_displayed_let_name_in :
  'a Generator.t -> Environ.env -> evar_map -> renaming_flags -> 'a -> Name.t -> Name.t * 'a

(* Generic function expecting a "not occurn" function *)
val compute_displayed_name_in_gen :
  'a Generator.t -> (evar_map -> int -> 'constr -> bool) ->
  Environ.env -> evar_map -> 'a -> Name.t -> 'constr -> Name.t * 'a
