(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Environ
(*i*)

(* Type errors. \label{typeerrors} *)

(*i Rem: NotEnoughAbstractionInFixBody should only occur with "/i" Fix
    notation i*)
type guard_error =
  (* Fixpoints *)
  | NotEnoughAbstractionInFixBody
  | RecursionNotOnInductiveType of constr
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
  | NotGuardedForm of constr

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
  | ElimArity of inductive * sorts_family list * constr * unsafe_judgment
      * (sorts_family * sorts_family * arity_error) option
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
  env -> inductive -> sorts_family list -> constr -> unsafe_judgment -> 
      (sorts_family * sorts_family * arity_error) option -> 'a

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

