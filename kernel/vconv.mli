(*i*)
open Names
open Term
open Environ
open Reduction
(*i*)

(***********************************************************************)
(*s conversion functions *)
val vconv : conv_pb -> types conversion_function

(***********************************************************************)
(*s Reduction functions *)
val cbv_vm : env -> constr -> types -> constr
