(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Evd
open Environ
open EConstr
open Inductiveops
open Glob_term
open Evardefine

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

val error_wrong_numarg_constructor : ?loc:Loc.t -> env -> constructor -> int -> 'a

val error_wrong_numarg_inductive   : ?loc:Loc.t -> env -> inductive -> int -> 'a

val irrefutable : env -> cases_pattern -> bool

(** {6 Compilation primitive. } *)

val compile_cases :
  ?loc:Loc.t -> program_mode:bool -> case_style ->
  (type_constraint -> GlobEnv.t -> evar_map -> glob_constr -> evar_map * unsafe_judgment) * evar_map ->
  type_constraint ->
  GlobEnv.t -> glob_constr option * tomatch_tuples * cases_clauses ->
  evar_map * unsafe_judgment

val constr_of_pat : 
           Environ.env ->
           Evd.evar_map ->
           rel_context ->
           Glob_term.cases_pattern ->
           Names.Id.Set.t ->
           Evd.evar_map * Glob_term.cases_pattern *
           (rel_context * constr *
            (types * constr list) * Glob_term.cases_pattern) *
           Names.Id.Set.t

type 'a rhs =
    { rhs_env    : GlobEnv.t;
      rhs_vars   : Id.Set.t;
      avoid_ids  : Id.Set.t;
      it         : 'a option}

type 'a equation =
    { patterns     : cases_pattern list;
      rhs          : 'a rhs;
      alias_stack  : Name.t list;
      eqn_loc      : Loc.t option;
      used         : bool ref }

type 'a matrix = 'a equation list

(* 1st argument of IsInd is the original ind before extracting the summary *)
type tomatch_type =
  | IsInd of types * inductive_type * Name.t list
  | NotInd of constr option * types

(* spiwack: The first argument of [Pushed] is [true] for initial
   Pushed and [false] otherwise. Used to decide whether the term being
   matched on must be aliased in the variable case (only initial
   Pushed need to be aliased). The first argument of [Alias] is [true]
   if the alias was introduced by an initial pushed and [false]
   otherwise.*)
type tomatch_status =
  | Pushed of (bool*((constr * tomatch_type) * int list * Name.t))
  | Alias of (bool * (Name.t * constr * (constr * types)))
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
    { env       : GlobEnv.t;
      pred      : constr;
      tomatch   : tomatch_stack;
      history   : pattern_continuation;
      mat       : 'a matrix;
      caseloc   : Loc.t option;
      casestyle : case_style;
      typing_function: type_constraint -> GlobEnv.t -> evar_map -> 'a option -> evar_map * unsafe_judgment }

val compile : program_mode:bool -> evar_map -> 'a pattern_matching_problem -> evar_map * unsafe_judgment

val prepare_predicate : ?loc:Loc.t -> program_mode:bool ->
           (type_constraint ->
            GlobEnv.t -> Evd.evar_map -> glob_constr -> Evd.evar_map * unsafe_judgment) ->
           GlobEnv.t ->
           Evd.evar_map ->
           (types * tomatch_type) list ->
           rel_context list ->
           constr option ->
           glob_constr option -> (Evd.evar_map * (Name.t * Name.t list) list * constr) list

val make_return_predicate_ltac_lvar : GlobEnv.t -> Evd.evar_map -> Name.t ->
  Glob_term.glob_constr -> constr -> GlobEnv.t
