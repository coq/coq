(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Names
open Term
open Sign
open Environ
open Rawterm
open Termops
open Mod_subst
(*i*)

val subst_cases_pattern : substitution -> cases_pattern -> cases_pattern

val subst_rawconstr : substitution -> rawconstr -> rawconstr

(* [detype isgoal avoid ctx c] turns a closed [c], into a rawconstr *)
(* de Bruijn indexes are turned to bound names, avoiding names in [avoid] *)
(* [isgoal] tells if naming must avoid global-level synonyms as intro does *)
(* [ctx] gives the names of the free variables *)

val detype : bool -> identifier list -> names_context -> constr -> rawconstr

val detype_case : 
  bool -> ('a -> rawconstr) ->
  (constructor array -> int array -> 'a array -> 
    (loc * identifier list * cases_pattern list * rawconstr) list) ->
  ('a -> int -> bool) ->
  identifier list -> inductive * case_style * int * int array * int ->
    'a option -> 'a -> 'a array -> rawconstr

val detype_sort : sorts -> rawsort

(* look for the index of a named var or a nondep var as it is renamed *)
val lookup_name_as_renamed  : env -> constr -> identifier -> int option
val lookup_index_as_renamed : env -> constr -> int -> int option

val set_detype_anonymous : (loc -> int -> rawconstr) -> unit
val force_wildcard : unit -> bool
val synthetize_type : unit -> bool
val force_if : case_info -> bool
val force_let : case_info -> bool

(* Utilities to transform kernel cases to simple pattern-matching problem *)

val it_destRLambda_or_LetIn_names : int -> rawconstr -> name list * rawconstr
val simple_cases_matrix_of_branches : 
  inductive -> int list -> rawconstr list -> cases_clauses
val return_type_of_predicate :
  inductive -> int -> int -> rawconstr -> predicate_pattern * rawconstr option

