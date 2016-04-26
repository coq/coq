(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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
  | UnusedClause of cases_pattern list
  | NonExhaustive of cases_pattern list
  | CannotInferPredicate of (constr * types) array

exception PatternMatchingError of env * evar_map * pattern_matching_error

val error_wrong_numarg_constructor_loc : Loc.t -> env -> constructor -> int -> 'a

val error_wrong_numarg_inductive_loc : Loc.t -> env -> inductive -> int -> 'a

val irrefutable : env -> cases_pattern -> bool

(** {6 Compilation primitive. } *)

val compile_cases :
  Loc.t -> case_style ->
  (type_constraint -> env -> evar_map ref -> glob_constr -> unsafe_judgment) * evar_map ref ->
  type_constraint ->
  env -> glob_constr option * tomatch_tuples * cases_clauses ->
  unsafe_judgment

val constr_of_pat : 
           Environ.env ->
           Evd.evar_map ref ->
           Context.Rel.Declaration.t list ->
           Glob_term.cases_pattern ->
           Names.Id.t list ->
           Glob_term.cases_pattern *
           (Context.Rel.Declaration.t list * Term.constr *
            (Term.types * Term.constr list) * Glob_term.cases_pattern) *
           Names.Id.t list
