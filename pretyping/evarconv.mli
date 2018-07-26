(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
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
val default_flags_of : ?subterm_ts:transparent_state -> transparent_state -> unify_flags

type unify_fun = unify_flags ->
  env -> evar_map -> conv_pb -> constr -> constr -> Evarsolve.unification_result

val conv_fun : unify_fun -> unify_flags -> Evarsolve.conv_fun

exception UnableToUnify of evar_map * Pretype_errors.unification_error

(** {6 Main unification algorithm for type inference. } *)

(** returns exception NotUnifiable with best known evar_map if not unifiable *)
val the_conv_x     : env -> ?ts:TransparentState.t -> constr -> constr -> evar_map -> evar_map
val the_conv_x_leq : env -> ?ts:TransparentState.t -> constr -> constr -> evar_map -> evar_map

(** Allows to pass arbitrary flags to the unifier *)
val unify : unify_flags -> env -> evar_map -> constr -> constr -> evar_map
val unify_leq : unify_flags -> env -> evar_map -> constr -> constr -> evar_map

(** @raises a PretypeError if it cannot unify *)
val unify_with_heuristics : unify_flags -> with_ho:bool ->
                            env -> evar_map -> conv_pb -> constr -> constr -> evar_map

(** The same function resolving evars by side-effect and
   catching the exception *)
val conv : env -> ?ts:TransparentState.t -> evar_map -> constr -> constr -> evar_map option
val cumul : env -> ?ts:TransparentState.t -> evar_map -> constr -> constr -> evar_map option

(** {6 Unification heuristics. } *)

(** Try heuristics to solve pending unification problems and to solve
    evars with candidates *)

val solve_unif_constraints_with_heuristics :
  env -> ?flags:unify_flags -> ?with_ho:bool -> evar_map -> evar_map

(** Check all pending unification problems are solved and raise an
    error otherwise *)

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

val second_order_matching : TransparentState.t -> env -> evar_map ->
  EConstr.existential -> occurrences option list -> constr -> evar_map * bool

(** Declare function to enforce evars resolution by using typing constraints *)

val set_solve_evars : (env -> evar_map -> constr -> evar_map * constr) -> unit

(** Override default [evar_conv_x] algorithm. *)
val set_evar_conv : unify_fun -> unit

(** The default unification algorithm with evars and universes. *)
val evar_conv_x : unify_fun

(**/**)
(* For debugging *)
val evar_eqappr_x : ?rhs_is_already_stuck:bool -> unify_flags ->
  env -> evar_map ->
    conv_pb -> state * Cst_stack.t -> state * Cst_stack.t ->
      Evarsolve.unification_result
(**/**)

(** {6 Functions to deal with impossible cases } *)
val coq_unit_judge : env -> EConstr.unsafe_judgment Univ.in_universe_context_set
