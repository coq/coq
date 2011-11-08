(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Sign
open Environ
open Termops
open Reductionops
open Evd

(** returns exception Reduction.NotConvertible if not unifiable *)
val the_conv_x     : ?ts:transparent_state -> env -> constr -> constr -> evar_map -> evar_map
val the_conv_x_leq : ?ts:transparent_state -> env -> constr -> constr -> evar_map -> evar_map

(** The same function resolving evars by side-effect and
   catching the exception *)
val e_conv  : ?ts:transparent_state -> env -> evar_map ref -> constr -> constr -> bool
val e_cumul : ?ts:transparent_state -> env -> evar_map ref -> constr -> constr -> bool

(**/**)
(* For debugging *)
val evar_conv_x : transparent_state ->
  env -> evar_map -> conv_pb -> constr -> constr -> evar_map * bool
val evar_eqappr_x : transparent_state ->
  env -> evar_map ->
    conv_pb -> constr * constr list -> constr * constr list ->
      evar_map * bool
(**/**)

val consider_remaining_unif_problems : ?ts:transparent_state -> env -> evar_map -> evar_map

val check_conv_record : constr * types list -> constr * types list ->
  constr * constr list * (constr list * constr list) *
    (constr list * types list) *
    (constr list * types list) * constr *
    (int * constr)

val set_solve_evars : (env -> evar_map -> constr -> evar_map * constr) -> unit

val second_order_matching : transparent_state -> env -> evar_map -> 
  existential -> occurrences option list -> constr -> evar_map * bool
