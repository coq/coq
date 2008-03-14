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
open Evd
open Environ
open Inductiveops
open Rawterm
open Evarutil
(*i*)

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

(*s Compilation of pattern-matching. *)

module type S = sig
  val compile_cases :
    loc ->
    (type_constraint -> env -> rawconstr -> unsafe_judgment) * evar_defs ref ->
    type_constraint -> 
    env -> rawconstr option * tomatch_tuple * cases_clauses ->
    unsafe_judgment
end

module Cases_F(C : Coercion.S) : S
