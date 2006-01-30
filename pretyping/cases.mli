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

val error_wrong_numarg_constructor_loc : loc -> env -> constructor -> int -> 'a

val error_wrong_numarg_inductive_loc : loc -> env -> inductive -> int -> 'a

(*s Used for old cases in pretyping *)

val branch_scheme : 
  env -> evar_defs ref -> bool -> inductive_family -> constr array

type ml_case_error =
  | MlCaseAbsurd
  | MlCaseDependent

exception NotInferable of ml_case_error

val pred_case_ml : (* raises [NotInferable] if not inferable *)
  env -> evar_map -> bool -> inductive_type -> int * types -> constr 

(*s Compilation of pattern-matching. *)

val compile_cases :
  loc ->
  (type_constraint -> env -> rawconstr -> unsafe_judgment) *
  evar_defs ref ->
  type_constraint -> 
  env ->
  rawconstr option *
  (rawconstr * (name * (loc * inductive * name list) option)) list *
  (loc * identifier list * cases_pattern list * rawconstr) list ->
  unsafe_judgment
