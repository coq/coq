(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ *)

(*i*)
open Names
open Term
open Sign
open Evd
open Environ
open Libnames
open Rawterm
open Pattern
open Coqast
open Topconstr
open Termops
(*i*)

(*s Translation from front abstract syntax of term to untyped terms (rawconstr)

   The translation performs:

   - resolution of names :
      - check all variables are bound
      - make absolute the references to global objets
   - resolution of symbolic notations using scopes
   - insert existential variables for implicit arguments
*)

(* To interpret implicits and arg scopes of recursive variables in
   inductive types and recursive definitions *)
type var_internalisation_data =
    identifier list * Impargs.implicits_list * scope_name option list

type implicits_env = (identifier * var_internalisation_data) list
type full_implicits_env = identifier list * implicits_env

type ltac_sign = 
  identifier list * (identifier * identifier option) list

type ltac_env = 
  (identifier * constr) list * (identifier * identifier option) list

(* Interprets global names, including syntactic defs and section variables *)
val interp_rawconstr     : evar_map -> env -> constr_expr -> rawconstr
val interp_rawconstr_gen : bool -> evar_map -> env -> 
    bool -> ltac_sign -> constr_expr -> rawconstr

(*s Composing the translation with typing *)
val interp_constr        : evar_map -> env -> constr_expr -> constr
val interp_casted_constr : evar_map -> env -> constr_expr -> types -> constr
val interp_type          : evar_map -> env -> constr_expr -> types
val interp_binder        : evar_map -> env -> name -> constr_expr -> types
val interp_openconstr    : evar_map -> env -> constr_expr -> evar_map * constr
val interp_casted_openconstr    :
  evar_map -> env -> constr_expr -> constr -> evar_map * constr

(* [interp_type_with_implicits] extends [interp_type] by allowing
   implicits arguments in the ``rel'' part of [env]; the extra
   argument associates a list of implicit positions to identifiers
   declared in the rel_context of [env] *)
val interp_type_with_implicits : 
  evar_map -> env -> full_implicits_env -> constr_expr -> types

val interp_casted_constr_with_implicits :
  evar_map -> env -> implicits_env -> constr_expr -> types -> constr

val interp_rawconstr_with_implicits :
  evar_map -> env -> identifier list -> implicits_env -> constr_expr -> 
    rawconstr

(*s Build a judgement from *)
val judgment_of_rawconstr : evar_map -> env -> constr_expr -> unsafe_judgment
val type_judgment_of_rawconstr :
  evar_map -> env -> constr_expr -> unsafe_type_judgment

(* Interprets a constr according to two lists of instantiations (variables and
  metas), possibly casting it*)
val interp_constr_gen     :
  evar_map -> env -> ltac_env -> constr_expr -> constr option -> constr

(* Interprets a constr according to two lists of instantiations (variables and
  metas), possibly casting it, and turning unresolved evar into metas*)
val interp_openconstr_gen     :
  evar_map -> env -> ltac_env ->
    constr_expr -> constr option -> evar_map * constr

(* Interprets constr patterns according to a list of instantiations
  (variables)*)
val interp_constrpattern_gen : evar_map -> env -> identifier list ->
  constr_expr -> patvar list * constr_pattern

val interp_constrpattern : 
  evar_map -> env -> constr_expr -> patvar list * constr_pattern

val interp_reference : ltac_sign -> reference -> rawconstr

(* Locating references of constructions, possibly via a syntactic definition *)

val locate_reference : qualid -> global_reference
val is_global : identifier -> bool
val construct_reference : named_context -> identifier -> constr
val global_reference : identifier -> constr
val global_reference_in_absolute_module : dir_path -> identifier -> constr

(* Interprets into a abbreviatable constr *)
val interp_aconstr : implicits_env -> identifier list -> constr_expr ->
  interpretation

(* Globalization leak for Grammar *)
val for_grammar : ('a -> 'b) -> 'a -> 'b

(* Coqdoc utility functions *)
type coqdoc_state
val coqdoc_freeze : unit -> coqdoc_state
val coqdoc_unfreeze : coqdoc_state -> unit

(* For v8 translation *)
val set_temporary_implicits_in :
  (identifier * Impargs.implicits_list) list -> unit
