(*i*)
open Names
open Term
open Environ
open Reduction
(*i*)

(***********************************************************************)
(*s conversion functions *)
val use_vm : unit -> bool
val set_use_vm : bool -> unit
val vconv : conv_pb -> types conversion_function

(***********************************************************************)
(*s Reduction functions *)
val cbv_vm : env -> constr -> types -> constr





val nf_val : env -> values -> types -> constr

val nf_whd : env -> Vm.whd -> types -> constr

val nf_stk : env -> constr -> types -> Vm.stack  -> constr
       
val nf_args : env -> Vm.arguments -> types ->  types * constr array

val nf_bargs : env -> Vm.vblock -> types -> constr array

val nf_fun : env -> Vm.vfun -> types -> constr

val nf_fix : env -> Vm.vfix -> constr 
  
val nf_cofix : env -> Vm.vcofix -> constr

  
