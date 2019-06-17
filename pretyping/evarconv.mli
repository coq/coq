(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open EConstr
open Environ
open Reductionops
open Evd
open Locus

(** {4 Unification for type inference. } *)

type unify_flags = Evarsolve.unify_flags

(** The default subterm transparent state is no unfoldings *)
val default_flags_of : ?subterm_ts:TransparentState.t -> TransparentState.t -> unify_flags

type unify_fun = unify_flags ->
  env -> evar_map -> conv_pb -> constr -> constr -> Evarsolve.unification_result

val conv_fun : unify_fun -> Evarsolve.unifier

exception UnableToUnify of evar_map * Pretype_errors.unification_error

(** {6 Main unification algorithm for type inference. } *)

(** There are two variants for unification: one that delays constraints outside its capabilities
    ([unify_delay]) and another that tries to solve such remaining constraints using
    heuristics ([unify]). *)

(** These functions allow to pass arbitrary flags to the unifier and can delay constraints.
    In case the flags are not specified, they default to
    [default_flags_of TransparentState.full] currently.

    In case of success, the two terms are hence unifiable only if the remaining constraints
    can be solved or [check_problems_are_solved] is true.

    @raises UnableToUnify in case the two terms do not unify *)

val unify_delay : ?flags:unify_flags -> env -> evar_map -> constr -> constr -> evar_map
val unify_leq_delay : ?flags:unify_flags -> env -> evar_map -> constr -> constr -> evar_map

(** This function also calls [solve_unif_constraints_with_heuristics] to resolve any remaining
    constraints. In case of success the two terms are unified without condition.

    The with_ho option tells if higher-order unification should be tried to resolve the
    constraints.

    @raises a PretypeError if it cannot unify *)
val unify : ?flags:unify_flags -> ?with_ho:bool ->
  env -> evar_map -> conv_pb -> constr -> constr -> evar_map

(** {6 Unification heuristics. } *)

(** Try heuristics to solve pending unification problems and to solve
   evars with candidates.

   The with_ho option tells if higher-order unification should be tried
   to resolve the constraints.

    @raises a PretypeError if it fails to resolve some problem *)

val solve_unif_constraints_with_heuristics :
  env -> ?flags:unify_flags -> ?with_ho:bool -> evar_map -> evar_map

(** Check all pending unification problems are solved and raise a
    PretypeError otherwise *)

val check_problems_are_solved : env -> evar_map -> unit

(** Check if a canonical structure is applicable *)

val check_conv_record : env -> evar_map -> 
  state -> state ->
  Univ.ContextSet.t * (constr * constr) 
  * constr * constr list * (constr Stack.t * constr Stack.t) *
    (constr Stack.t * constr Stack.t) *
    (constr Stack.t * constr Stack.t) * constr *
    (int option * constr)

(** Try to solve problems of the form ?x[args] = c by second-order
    matching, using typing to select occurrences *)

type occurrence_match_test =
  env -> evar_map -> constr -> (* Used to precompute the local tests *)
  env -> evar_map -> int -> constr -> constr -> bool * evar_map

(** When given the choice of abstracting an occurrence or leaving it,
    force abstration. *)

type occurrence_selection =
  | AtOccurrences of occurrences
  | Unspecified of Abstraction.abstraction

(** By default, unspecified, not preferring abstraction.
    This provides the most general solutions. *)
val default_occurrence_selection : occurrence_selection

type occurrences_selection =
  occurrence_match_test * occurrence_selection list

val default_occurrence_test : frozen_evars:Evar.Set.t -> TransparentState.t -> occurrence_match_test

(** [default_occurrence_selection n]
    Gives the default test and occurrences for [n] arguments *)
val default_occurrences_selection : ?frozen_evars:Evar.Set.t (* By default, none *) ->
  TransparentState.t -> int -> occurrences_selection

val second_order_matching : unify_flags -> env -> evar_map ->
  EConstr.existential -> occurrences_selection -> constr -> evar_map * bool

(** Declare function to enforce evars resolution by using typing constraints *)

val set_solve_evars : (env -> evar_map -> constr -> evar_map * constr) -> unit

(** Override default [evar_conv_x] algorithm. *)
val set_evar_conv : unify_fun -> unit

(** The default unification algorithm with evars and universes. *)
val evar_conv_x : unify_fun

val evar_unify : Evarsolve.unifier

(**/**)
(* For debugging *)
val evar_eqappr_x : ?rhs_is_already_stuck:bool -> unify_flags ->
  env -> evar_map ->
    conv_pb -> state -> state ->
      Evarsolve.unification_result

val occur_rigidly : Evarsolve.unify_flags ->
  'a -> Evd.evar_map -> Evar.t * 'b -> EConstr.t -> bool
(**/**)

(** {6 Functions to deal with impossible cases } *)
val coq_unit_judge : env -> EConstr.unsafe_judgment Univ.in_universe_context_set
