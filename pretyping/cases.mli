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
open Evd
open Environ
open Inductiveops
open Rawterm
open Evarutil

(** {5 Compilation of pattern-matching } *)

(** {6 Pattern-matching errors } *)
type pattern_matching_error =
  | BadPattern of constructor * constr
  | BadConstructor of constructor * inductive
  | WrongNumargConstructor of constructor * int
  | WrongNumargInductive of inductive * int
  | WrongPredicateArity of constr * constr * constr
  | NeedsInversion of constr * constr
  | UnusedClause of cases_pattern list
  | NonExhaustive of cases_pattern list
  | CannotInferPredicate of (constr * types) array

exception PatternMatchingError of env * pattern_matching_error

val raise_pattern_matching_error : (loc * env * pattern_matching_error) -> 'a

val error_wrong_numarg_constructor_loc : loc -> env -> constructor -> int -> 'a

val error_wrong_numarg_inductive_loc : loc -> env -> inductive -> int -> 'a

val error_bad_constructor_loc : loc -> constructor -> inductive -> 'a

val error_bad_pattern_loc : loc -> constructor -> constr -> 'a

val error_wrong_predicate_arity_loc : loc -> env -> constr -> constr -> constr -> 'a

val error_needs_inversion : env -> constr -> types -> 'a

(** {6 Compilation primitive. } *)
type alias_constr =
  | DepAlias
  | NonDepAlias
type dep_status = KnownDep | KnownNotDep | DepUnknown
type tomatch_type =
  | IsInd of types * inductive_type * name list
  | NotInd of constr option * types
type tomatch_status =
  | Pushed of ((constr * tomatch_type) * int list * (name * dep_status))
  | Alias of (constr * constr * alias_constr * constr)
  | Abstract of rel_declaration

module type S = sig
  val compile_cases :
    loc -> case_style ->
    (type_constraint -> env -> evar_map ref -> glob_constr -> unsafe_judgment) * evar_map ref ->
    type_constraint ->
    env -> glob_constr option * tomatch_tuples * cases_clauses ->
    unsafe_judgment
end

module Cases_F(C : Coercion.S) : S
