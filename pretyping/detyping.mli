(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Term
open Sign
open Environ
open Rawterm
open Termops
open Mod_subst

val subst_cases_pattern : substitution -> cases_pattern -> cases_pattern

val subst_glob_constr : substitution -> glob_constr -> glob_constr

(** [detype isgoal avoid ctx c] turns a closed [c], into a glob_constr 
   de Bruijn indexes are turned to bound names, avoiding names in [avoid] 
   [isgoal] tells if naming must avoid global-level synonyms as intro does 
   [ctx] gives the names of the free variables *)

val detype : bool -> identifier list -> names_context -> constr -> glob_constr

val detype_case :
  bool -> ('a -> glob_constr) ->
  (constructor array -> int array -> 'a array ->
    (loc * identifier list * cases_pattern list * glob_constr) list) ->
  ('a -> int -> bool) ->
  identifier list -> inductive * case_style * int * int array * int ->
    'a option -> 'a -> 'a array -> glob_constr

val detype_sort : sorts -> rawsort

val detype_rel_context : constr option -> identifier list -> names_context ->
  rel_context -> glob_decl list

(** look for the index of a named var or a nondep var as it is renamed *)
val lookup_name_as_displayed  : env -> constr -> identifier -> int option
val lookup_index_as_renamed : env -> constr -> int -> int option

val set_detype_anonymous : (loc -> int -> glob_constr) -> unit
val force_wildcard : unit -> bool
val synthetize_type : unit -> bool

(** Utilities to transform kernel cases to simple pattern-matching problem *)

val it_destRLambda_or_LetIn_names : int -> glob_constr -> name list * glob_constr
val simple_cases_matrix_of_branches :
  inductive -> int list -> glob_constr list -> cases_clauses
val return_type_of_predicate :
  inductive -> int -> int -> glob_constr -> predicate_pattern * glob_constr option
