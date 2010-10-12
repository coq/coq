(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Sign
open Environ
open Reductionops
open Evd

(** returns exception Reduction.NotConvertible if not unifiable *)
val the_conv_x     : env -> constr -> constr -> evar_map -> evar_map
val the_conv_x_leq : env -> constr -> constr -> evar_map -> evar_map

(** The same function resolving evars by side-effect and
   catching the exception *)
val e_conv  : env -> evar_map ref -> constr -> constr -> bool
val e_cumul : env -> evar_map ref -> constr -> constr -> bool

(**/**)
(* For debugging *)
val evar_conv_x :
  env -> evar_map -> conv_pb -> constr -> constr -> evar_map * bool
val evar_eqappr_x :
  env -> evar_map ->
    conv_pb -> constr * constr list -> constr * constr list ->
      evar_map * bool
(**/**)

val consider_remaining_unif_problems : env -> evar_map -> evar_map

val check_conv_record : constr * types list -> constr * types list ->
  constr * constr list * (constr list * constr list) *
    (constr list * types list) *
    (constr list * types list) * constr *
    (int * constr)
