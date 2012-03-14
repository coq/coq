(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Errors
open Pp
open Names
open Term
open Evd
open Environ
open Inductiveops
open Glob_term
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

val compile_cases :
  loc -> case_style ->
  (type_constraint -> env -> evar_map ref -> glob_constr -> unsafe_judgment) * evar_map ref ->
  type_constraint ->
  env -> glob_constr option * tomatch_tuples * cases_clauses ->
  unsafe_judgment

val constr_of_pat : 
           Environ.env ->
           Evd.evar_map ref ->
           Term.rel_declaration list ->
           Glob_term.cases_pattern ->
           Names.identifier list ->
           Glob_term.cases_pattern *
           (Term.rel_declaration list * Term.constr *
            (Term.types * Term.constr list) * Glob_term.cases_pattern) *
           Names.identifier list

type 'a rhs =
    { rhs_env    : env;
      rhs_vars   : identifier list;
      avoid_ids  : identifier list;
      it         : 'a option}

type 'a equation =
    { patterns     : cases_pattern list;
      rhs          : 'a rhs;
      alias_stack  : name list;
      eqn_loc      : loc;
      used         : bool ref }

type 'a matrix = 'a equation list

(* 1st argument of IsInd is the original ind before extracting the summary *)
type tomatch_type =
  | IsInd of types * inductive_type * name list
  | NotInd of constr option * types

type tomatch_status =
  | Pushed of ((constr * tomatch_type) * int list * name)
  | Alias of (name * constr * (constr * types))
  | NonDepAlias
  | Abstract of int * rel_declaration

type tomatch_stack = tomatch_status list

(* We keep a constr for aliases and a cases_pattern for error message *)

type pattern_history =
  | Top
  | MakeConstructor of constructor * pattern_continuation

and pattern_continuation =
  | Continuation of int * cases_pattern list * pattern_history
  | Result of cases_pattern list

type 'a pattern_matching_problem =
    { env       : env;
      evdref    : evar_map ref;
      pred      : constr;
      tomatch   : tomatch_stack;
      history   : pattern_continuation;
      mat       : 'a matrix;
      caseloc   : loc;
      casestyle : case_style;
      typing_function: type_constraint -> env -> evar_map ref -> 'a option -> unsafe_judgment }


val compile : 'a pattern_matching_problem -> Environ.unsafe_judgment
