
(* $Id$ *)

(*i*)
open Pp
open Names
open Term
open Sign
open Environ
(*i*)

(* Type errors. \label{typeerrors} *)

type type_error =
  | UnboundRel of int
  | NotAType of unsafe_judgment
  | BadAssumption of constr
  | ReferenceVariables of identifier
  | ElimArity of inductive * constr list * constr * constr * constr
      * (constr * constr * string) option
  | CaseNotInductive of constr * constr
  | NumberBranches of constr * constr * int
  | IllFormedBranch of constr * int * constr * constr
  | Generalization of (name * typed_type) * unsafe_judgment
  | ActualType of constr * constr * constr
  | CantApplyBadType of (int * constr * constr)
      * unsafe_judgment * unsafe_judgment list
  | CantApplyNonFunctional of unsafe_judgment * unsafe_judgment list
  | IllFormedRecBody of std_ppcmds * name list * int * constr array
  | IllTypedRecBody of int * name list * unsafe_judgment array 
      * typed_type array
  | NotInductive of constr
  | MLCase of string * constr * constr * constr * constr
  | CantFindCaseType of constr
  | OccurCheck of int * constr
  | NotClean of int * constr
  | VarNotFound of identifier
  | NotProduct of constr
  (* Pattern-matching errors *)
  | BadConstructor of constructor * inductive
  | WrongNumargConstructor of constructor_path * int
  | WrongPredicateArity of constr * int * int
  | NeedsInversion of constr * constr

exception TypeError of path_kind * context * type_error

val error_unbound_rel : path_kind -> env -> 'a Evd.evar_map -> int -> 'b

val error_not_type : path_kind -> env -> unsafe_judgment -> 'b

val error_assumption : path_kind -> env -> constr -> 'b
 
val error_reference_variables : path_kind -> env -> identifier -> 'b

val error_elim_arity : 
  path_kind -> env -> inductive -> constr list -> constr 
    -> constr -> constr -> (constr * constr * string) option -> 'b

val error_case_not_inductive : 
  path_kind -> env -> constr -> constr -> 'b

val error_number_branches : 
  path_kind -> env -> constr -> constr -> int -> 'b

val error_ill_formed_branch :
  path_kind -> env -> constr -> int -> constr -> constr -> 'b

val error_generalization :
  path_kind -> env -> 'a Evd.evar_map -> name * typed_type -> unsafe_judgment -> 'b

val error_actual_type :
  path_kind -> env -> constr -> constr -> constr -> 'b

val error_cant_apply_not_functional : 
  path_kind -> env -> unsafe_judgment -> unsafe_judgment list -> 'b

val error_cant_apply_bad_type : 
  path_kind -> env -> 'a Evd.evar_map -> int * constr * constr -> 
      unsafe_judgment -> unsafe_judgment list -> 'b

val error_ill_formed_rec_body :
  path_kind -> env -> std_ppcmds
    -> name list -> int -> constr array -> 'b

val error_ill_typed_rec_body  :
  path_kind -> env -> int -> name list -> unsafe_judgment array 
    -> typed_type array -> 'b

val error_not_inductive : path_kind -> env -> constr -> 'a

val error_ml_case : path_kind -> env -> 
  string -> constr -> constr -> constr -> constr -> 'a

val error_not_product : env -> constr -> 'a
