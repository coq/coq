
(* $Id$ *)

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
