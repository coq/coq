
(* $Id$ *)

open Pp
open Names
open Term
open Sign
open Environ
open Type_errors
open Rawterm

(* The type of errors raised by the pretyper *)

exception PreTypeError of loc * path_kind * context * type_error

val error_cant_find_case_type_loc : loc -> unsafe_env -> constr -> 'a

val error_number_branches_loc : 
  loc -> unsafe_env -> constr -> constr -> int -> 'b

val error_ill_formed_branch_loc : 
  loc -> path_kind -> unsafe_env -> constr -> int -> constr -> constr -> 'b
