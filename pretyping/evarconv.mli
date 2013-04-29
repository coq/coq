(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Context
open Environ
open Termops
open Reductionops
open Evd
open Locus

exception UnableToUnify of evar_map * Pretype_errors.unification_error

(** returns exception NotUnifiable with best known evar_map if not unifiable *)
val the_conv_x     : ?ts:transparent_state -> env -> constr -> constr -> evar_map -> evar_map
val the_conv_x_leq : ?ts:transparent_state -> env -> constr -> constr -> evar_map -> evar_map

(** The same function resolving evars by side-effect and
   catching the exception *)
val e_conv  : ?ts:transparent_state -> env -> evar_map ref -> constr -> constr -> bool
val e_cumul : ?ts:transparent_state -> env -> evar_map ref -> constr -> constr -> bool

(**/**)
(* For debugging *)
val evar_conv_x : transparent_state ->
  env -> evar_map -> conv_pb -> constr -> constr -> Evarsolve.unification_result
val evar_eqappr_x : ?rhs_is_already_stuck:bool -> transparent_state ->
  env -> evar_map ->
    conv_pb -> state * Cst_stack.t -> state * Cst_stack.t ->
      Evarsolve.unification_result
(**/**)

val consider_remaining_unif_problems : ?ts:transparent_state -> env -> evar_map -> evar_map

val check_conv_record : constr * types stack -> constr * types stack ->
  constr * constr list * (constr list * constr list) *
    (constr list * types list) *
    (constr stack * types stack) * constr *
    (int * constr)

val set_solve_evars : (env -> evar_map ref -> constr -> constr) -> unit

val second_order_matching : transparent_state -> env -> evar_map ->
  existential -> occurrences option list -> constr -> evar_map * bool
