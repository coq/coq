(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Environ
open Symbol
(*i*)

(* Type errors. \label{typeerrors} *)

(*i Rem: NotEnoughAbstractionInFixBody should only occur with "/i" Fix
    notation i*)
type guard_error =
  (* Fixpoints *)
  | NotEnoughAbstractionInFixBody
  | RecursionNotOnInductiveType
  | RecursionOnIllegalTerm of int * constr * int list * int list
  | NotEnoughArgumentsForFixCall of int
  (* CoFixpoints *)
  | CodomainNotInductiveType of constr
  | NestedRecursiveOccurrences
  | UnguardedRecursiveCall of constr
  | RecCallInTypeOfAbstraction of constr
  | RecCallInNonRecArgOfConstructor of constr
  | RecCallInTypeOfDef of constr
  | RecCallInCaseFun of constr
  | RecCallInCaseArg of constr
  | RecCallInCasePred of constr
  | NotGuardedForm

type arity_error =
  | NonInformativeToInformative
  | StrongEliminationOnNonSmallType
  | WrongArity

type type_error =
  | UnboundRel of int
  | UnboundVar of variable
  | NotAType of unsafe_judgment
  | BadAssumption of unsafe_judgment
  | ReferenceVariables of constr
  | ElimArity of inductive * types list * constr * unsafe_judgment
      * (constr * constr * arity_error) option
  | CaseNotInductive of unsafe_judgment
  | WrongCaseInfo of inductive * case_info
  | NumberBranches of unsafe_judgment * int
  | IllFormedBranch of constr * int * constr * constr
  | Generalization of (name * types) * unsafe_judgment
  | ActualType of unsafe_judgment * types
  | CantApplyBadType of
      (int * constr * constr) * unsafe_judgment * unsafe_judgment array
  | CantApplyNonFunctional of unsafe_judgment * unsafe_judgment array
  | IllFormedRecBody of guard_error * name array * int
  | IllTypedRecBody of
      int * name array * unsafe_judgment array * types array

exception TypeError of env * type_error

val error_unbound_rel : env -> int -> 'a

val error_unbound_var : env -> variable -> 'a

val error_not_type : env -> unsafe_judgment -> 'a

val error_assumption : env -> unsafe_judgment -> 'a
 
val error_reference_variables : env -> constr -> 'a

val error_elim_arity : 
  env -> inductive -> types list -> constr 
    -> unsafe_judgment -> (constr * constr * arity_error) option -> 'a

val error_case_not_inductive : env -> unsafe_judgment -> 'a

val error_number_branches : env -> unsafe_judgment -> int -> 'a

val error_ill_formed_branch : env -> constr -> int -> constr -> constr -> 'a

val error_generalization : env -> name * types -> unsafe_judgment -> 'a

val error_actual_type : env -> unsafe_judgment -> types -> 'a

val error_cant_apply_not_functional : 
  env -> unsafe_judgment -> unsafe_judgment array -> 'a

val error_cant_apply_bad_type : 
  env -> int * constr * constr -> 
      unsafe_judgment -> unsafe_judgment array -> 'a

val error_ill_formed_rec_body :
  env -> guard_error -> name array -> int -> 'a

val error_ill_typed_rec_body  :
  env -> int -> name array -> unsafe_judgment array -> types array -> 'a

(* Errors in symbol declarations *)

type symbol_error =
  | Type_not_compatible_with_arity
  | Type_not_compatible_with_eqth
  | Both_monotonic_and_antimonotonic of int

exception Symbol_error of symbol_error

val symbol_error : symbol_error -> 'a

(* Errors in rules declarations *)

type rule_error =
  | Not_a_symbol of kernel_name
  | Not_algebraic of constr
  | Not_a_symbol_or_a_constructor of constr
  | Term_not_admissible_in_RHS of constr
  | Not_symbol_headed
  | Not_linear
  | Recursive_call_not_smaller of status * constr array * constr array
  | Symbol_not_smaller of symbol * symbol
  | Variable_not_accessible of constr

exception Rule_error of (constr * constr) * env * env * rule_error

val rule_error : (constr * constr) -> env -> env -> rule_error -> 'a

(* Errors in conditions *)

type condition_error =
  | Not_locally_confluent

exception Condition_error of condition_error

val condition_error : condition_error -> 'a
