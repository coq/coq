
(* $Id$ *)

(*i*)
open Term
open Sign
open Environ
open Reduction
open Evarutil
(*i*)

val reset_problems : unit -> unit
val the_conv_x : unsafe_env -> 'a evar_defs -> constr -> constr -> bool
val the_conv_x_leq : unsafe_env -> 'a evar_defs -> constr -> constr -> bool


(* For debugging *)
val solve_pb : 'c evar_defs -> conv_pb * constr * constr -> bool
val evar_conv_x : 'c evar_defs -> context option ->
  conv_pb -> constr -> constr -> bool
val evar_eqappr_x : 'c evar_defs -> context option ->
  conv_pb -> constr * constr list -> constr * constr list -> bool
