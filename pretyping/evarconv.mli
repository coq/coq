(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Term
open Sign
open Environ
open Reduction
open Evarutil
(*i*)

val the_conv_x : env -> 'a evar_defs -> constr -> constr -> bool

val the_conv_x_leq : env -> 'a evar_defs -> constr -> constr -> bool

(*i For debugging *)
val evar_conv_x : env -> 'a evar_defs -> conv_pb -> constr -> constr -> bool
val evar_eqappr_x : 
  env -> 'a evar_defs ->
    conv_pb -> constr * constr list -> constr * constr list -> bool
(*i*)
