(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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
(*i*)

(*s Translation from front abstract syntax of term to untyped terms (rawconstr)

   The translation performs:

   - resolution of names :
      - check all variables are bound
      - make absolute the references to global objets
   - resolution of symbolic notations using scopes
   - insert existential variables for implicit arguments
*)

type implicits_env = (identifier * Impargs.implicits_list) list

(* Interprets global names, including syntactic defs and section variables *)
val interp_rawconstr     : evar_map -> env -> constr_expr -> rawconstr
val interp_rawconstr_gen : evar_map -> env -> implicits_env -> 
    bool -> identifier list -> constr_expr -> rawconstr

(*s Composing the translation with typing *)
val interp_constr        : evar_map -> env -> constr_expr -> constr
val interp_casted_constr : evar_map -> env -> constr_expr -> types -> constr
val interp_type          : evar_map -> env -> constr_expr -> types
val interp_openconstr    : evar_map -> env -> constr_expr -> evar_map * constr
val interp_casted_openconstr    :
  evar_map -> env -> constr_expr -> constr -> evar_map * constr

(* [interp_type_with_implicits] extends [interp_type] by allowing
   implicits arguments in the ``rel'' part of [env]; the extra
   argument associates a list of implicit positions to identifiers
   declared in the rel_context of [env] *)
val interp_type_with_implicits : 
  evar_map -> env -> implicits_env -> constr_expr -> types

(*s Build a judgement from *)
val judgment_of_rawconstr : evar_map -> env -> constr_expr -> unsafe_judgment
val type_judgment_of_rawconstr :
  evar_map -> env -> constr_expr -> unsafe_type_judgment

(* Interprets a constr according to two lists of instantiations (variables and
  metas), possibly casting it*)
val interp_constr_gen     :
  evar_map -> env -> (identifier * constr) list ->
    (int * constr) list -> constr_expr -> constr option -> constr

(* Interprets a constr according to two lists of instantiations (variables and
  metas), possibly casting it, and turning unresolved evar into metas*)
val interp_openconstr_gen     :
  evar_map -> env -> (identifier * constr) list ->
    (int * constr) list -> constr_expr -> constr option -> evar_map * constr

(* Interprets constr patterns according to a list of instantiations
  (variables)*)
val interp_constrpattern_gen :
  evar_map -> env -> (identifier * constr) list -> constr_expr ->
    int list * constr_pattern

val interp_constrpattern : 
  evar_map -> env -> constr_expr -> int list * constr_pattern

val interp_reference : identifier list -> reference -> rawconstr

(* Interprets into a abbreviatable constr *)
val interp_aconstr : constr_expr -> aconstr

(* Globalization leak for Grammar *)
val for_grammar : ('a -> 'b) -> 'a -> 'b
