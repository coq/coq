
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

(*s The type of errors raised by the pretyper *)

val error_var_not_found_loc :
  loc -> path_kind -> identifier -> 'a

val error_global_not_found_loc :
  loc -> qualid -> 'a

val error_cant_find_case_type_loc : 
  loc -> env -> constr -> 'a

val error_ill_formed_branch_loc : 
  loc -> path_kind -> env -> constr -> int -> constr -> constr -> 'b

val error_actual_type_loc :
  loc -> env -> constr -> constr -> constr -> 'b

val error_cant_apply_not_functional_loc : 
  loc -> env -> unsafe_judgment -> unsafe_judgment list -> 'b

val error_cant_apply_bad_type_loc : 
  loc -> env -> int * constr * constr -> 
      unsafe_judgment -> unsafe_judgment list -> 'b

val error_number_branches_loc : 
  loc -> path_kind -> env -> constr -> constr -> int -> 'b

val error_case_not_inductive_loc :
  loc -> path_kind -> env -> constr -> constr -> 'b

(*s Pattern-matching errors *)

val error_bad_pattern_loc : 
  loc -> path_kind -> constructor -> constr -> 'b

val error_bad_constructor_loc : 
  loc -> path_kind -> constructor -> inductive -> 'b

val error_wrong_numarg_constructor_loc : 
  loc -> path_kind -> constructor_path -> int -> 'b

val error_wrong_predicate_arity_loc :
  loc -> path_kind -> env -> constr -> int -> int -> 'b

val error_needs_inversion : path_kind -> env -> constr -> constr -> 'a


(*s Implicit arguments synthesis errors *)

val error_unexpected_type_loc : loc -> env -> constr -> constr -> 'b

val error_occur_check : path_kind -> env -> int -> constr -> 'a

val error_not_clean : path_kind -> env -> int -> constr -> 'a


