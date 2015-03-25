open Names
open Cbytecodes
open Cemitcodes 
open Term
open Declarations
open Pre_env



val compile : bool -> env -> constr -> (bytecodes * bytecodes * fv) option
                              (* init, fun, fv *)

val compile_constant_body :
    bool -> 
    env -> constr_substituted option -> bool -> bool -> body_code option
                                 (* opaque *) (* boxed *)
			   

