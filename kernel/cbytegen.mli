open Names
open Cbytecodes
open Cemitcodes 
open Term
open Declarations
open Environ



val compile : env -> constr -> bytecodes * bytecodes * fv
                              (* init, fun, fv *)

val compile_constant_body : 
    env -> constant -> constr_substituted option -> bool -> bool -> body_code
                                              (* opaque *) (* boxed *)

