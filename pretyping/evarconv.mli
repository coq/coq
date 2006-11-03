(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Term
open Sign
open Environ
open Reductionops
open Evd
(*i*)

(* returns exception Reduction.NotConvertible if not unifiable *)
val the_conv_x     : env -> constr -> constr -> evar_defs -> evar_defs
val the_conv_x_leq : env -> constr -> constr -> evar_defs -> evar_defs

(* The same function resolving evars by side-effect and 
   catching the exception *)
val e_conv  : env -> evar_defs ref -> constr -> constr -> bool
val e_cumul : env -> evar_defs ref -> constr -> constr -> bool

(*i For debugging *)
val evar_conv_x :
  env -> evar_defs -> conv_pb -> constr -> constr -> evar_defs * bool
val evar_eqappr_x : 
  env -> evar_defs ->
    conv_pb -> constr * constr list -> constr * constr list ->
      evar_defs * bool
(*i*)

val consider_remaining_unif_problems : env -> evar_defs -> evar_defs * bool
