
(* $Id$ *)

(*i*)
open Pp
open Names
open Term
open Sign
open Environ
open Type_errors
open Rawterm
(*i*)

(* The type of errors raised by the pretyper *)

exception PretypeError of loc * path_kind * context * type_error

val error_var_not_found_loc :
  loc -> path_kind -> identifier -> 'a

val error_cant_find_case_type_loc : 
  loc -> env -> constr -> 'a

val error_ill_formed_branch_loc : 
  loc -> path_kind -> env -> constr -> int -> constr -> constr -> 'b

val error_number_branches_loc : 
  loc -> path_kind -> env -> constr -> constr -> int -> 'b

val error_case_not_inductive_loc :
  loc -> path_kind -> env -> constr -> constr -> 'b

(* Pattern-matching errors *)

val error_bad_constructor_loc : 
  loc -> path_kind -> constructor_path -> inductive_path -> 'b

val error_wrong_numarg_constructor_loc : 
  loc -> path_kind -> constructor_path -> int -> 'b

val error_wrong_predicate_arity_loc :
  loc -> path_kind -> env -> constr -> int -> int -> 'b

val error_needs_inversion : path_kind -> env -> constr -> constr -> 'a


(* Implicit arguments synthesis errors *)

val error_occur_check : path_kind -> env -> int -> constr -> 'a

val error_not_clean : path_kind -> env -> int -> constr -> 'a


