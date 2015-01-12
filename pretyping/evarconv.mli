(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Environ
open Reductionops
open Evd
open Locus

(** {4 Unification for type inference. } *)

exception UnableToUnify of evar_map * Pretype_errors.unification_error

(** {6 Main unification algorithm for type inference. } *)

(** returns exception NotUnifiable with best known evar_map if not unifiable *)
val the_conv_x     : env -> ?ts:transparent_state -> constr -> constr -> evar_map -> evar_map
val the_conv_x_leq : env -> ?ts:transparent_state -> constr -> constr -> evar_map -> evar_map

(** The same function resolving evars by side-effect and
   catching the exception *)
val e_conv  : env -> ?ts:transparent_state -> evar_map ref -> constr -> constr -> bool
val e_cumul : env -> ?ts:transparent_state -> evar_map ref -> constr -> constr -> bool

(** {6 Unification heuristics. } *)

(** Try heuristics to solve pending unification problems and to solve
    evars with candidates *)

val consider_remaining_unif_problems : env -> ?ts:transparent_state -> evar_map -> evar_map

(** Check all pending unification problems are solved and raise an
    error otherwise *)

val check_problems_are_solved : env -> evar_map -> unit

(** Check if a canonical structure is applicable *)

val check_conv_record : env -> evar_map -> 
  constr * types Stack.t -> constr * types Stack.t ->
  Univ.universe_context_set * (constr * constr) 
  * constr * constr list * (constr Stack.t * constr Stack.t) *
    (constr Stack.t * types Stack.t) *
    (constr Stack.t * types Stack.t) * constr *
    (int option * constr)

(** Try to solve problems of the form ?x[args] = c by second-order
    matching, using typing to select occurrences *)

val second_order_matching : transparent_state -> env -> evar_map ->
  existential -> occurrences option list -> constr -> evar_map * bool

(** Declare function to enforce evars resolution by using typing constraints *)

val set_solve_evars : (env -> evar_map ref -> constr -> constr) -> unit

type unify_fun = transparent_state ->
  env -> evar_map -> conv_pb -> constr -> constr -> Evarsolve.unification_result

(** Override default [evar_conv_x] algorithm. *)
val set_evar_conv : unify_fun -> unit

(** The default unification algorithm with evars and universes. *)
val evar_conv_x : unify_fun

(**/**)
(* For debugging *)
val evar_eqappr_x : ?rhs_is_already_stuck:bool -> transparent_state * bool ->
  env -> evar_map ->
    conv_pb -> state * Cst_stack.t -> state * Cst_stack.t ->
      Evarsolve.unification_result
(**/**)

