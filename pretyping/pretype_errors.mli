
(*i $Id$ i*)

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

type ml_case_error =
  | MlCaseAbsurd
  | MlCaseDependent

type pretype_error =
  (* Old Case *)
  | MlCase of ml_case_error
  | CantFindCaseType of constr
  (* Unification *)
  | OccurCheck of int * constr
  | NotClean of int * constr
  (* Pretyping *)
  | VarNotFound of identifier
  | UnexpectedType of constr * constr
  | NotProduct of constr

exception PretypeError of env * pretype_error

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

(*s Implicit arguments synthesis errors *)

val error_occur_check : env -> int -> constr -> 'a

val error_not_clean : env -> int -> constr -> 'a

(*s Ml Case errors *)

val error_ml_case_loc : loc -> env -> ml_case_error -> 'a

(*s Pretyping errors *)

val error_var_not_found_loc : loc -> identifier -> 'a

val error_unexpected_type_loc : loc -> env -> constr -> constr -> 'b

val error_not_product_loc : loc -> env -> constr -> 'a
