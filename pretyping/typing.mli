
(* $Id$ *)

(*i*)
open Term
open Environ
open Evd
(*i*)

(* This module provides the typing machine with existential variables
   (but without universes). *)

val type_of : env -> 'a evar_map -> constr -> constr

val execute_type : env -> 'a evar_map -> constr -> typed_type

val execute_rec_type : env -> 'a evar_map -> constr -> typed_type

