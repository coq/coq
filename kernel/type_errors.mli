(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Environ

(** Type errors. {% \label{%}typeerrors{% }%} *)

(*i Rem: NotEnoughAbstractionInFixBody should only occur with "/i" Fix
    notation i*)
type 'constr pguard_error =
  (** Fixpoints *)
  | NotEnoughAbstractionInFixBody
  | RecursionNotOnInductiveType of 'constr
  | RecursionOnIllegalTerm of int * (env * 'constr) * int list * int list
  | NotEnoughArgumentsForFixCall of int
  (** CoFixpoints *)
  | CodomainNotInductiveType of 'constr
  | NestedRecursiveOccurrences
  | UnguardedRecursiveCall of 'constr
  | RecCallInTypeOfAbstraction of 'constr
  | RecCallInNonRecArgOfConstructor of 'constr
  | RecCallInTypeOfDef of 'constr
  | RecCallInCaseFun of 'constr
  | RecCallInCaseArg of 'constr
  | RecCallInCasePred of 'constr
  | NotGuardedForm of 'constr
  | ReturnPredicateNotCoInductive of 'constr

type guard_error = constr pguard_error

type arity_error =
  | NonInformativeToInformative
  | StrongEliminationOnNonSmallType
  | WrongArity

type ('constr, 'types) ptype_error =
  | UnboundRel of int
  | UnboundVar of variable
  | NotAType of ('constr, 'types) punsafe_judgment
  | BadAssumption of ('constr, 'types) punsafe_judgment
  | ReferenceVariables of Id.t * 'constr
  | ElimArity of pinductive * Sorts.family list * 'constr * ('constr, 'types) punsafe_judgment
      * (Sorts.family * Sorts.family * arity_error) option
  | CaseNotInductive of ('constr, 'types) punsafe_judgment
  | WrongCaseInfo of pinductive * case_info
  | NumberBranches of ('constr, 'types) punsafe_judgment * int
  | IllFormedBranch of 'constr * pconstructor * 'constr * 'constr
  | Generalization of (Name.t * 'types) * ('constr, 'types) punsafe_judgment
  | ActualType of ('constr, 'types) punsafe_judgment * 'types
  | CantApplyBadType of
      (int * 'constr * 'constr) * ('constr, 'types) punsafe_judgment * ('constr, 'types) punsafe_judgment array
  | CantApplyNonFunctional of ('constr, 'types) punsafe_judgment * ('constr, 'types) punsafe_judgment array
  | IllFormedRecBody of 'constr pguard_error * Name.t array * int * env * ('constr, 'types) punsafe_judgment array
  | IllTypedRecBody of
      int * Name.t array * ('constr, 'types) punsafe_judgment array * 'types array
  | UnsatisfiedConstraints of Univ.Constraint.t
  | UndeclaredUniverse of Univ.Level.t

type type_error = (constr, types) ptype_error

exception TypeError of env * type_error

val error_unbound_rel : env -> int -> 'a

val error_unbound_var : env -> variable -> 'a

val error_not_type : env -> unsafe_judgment -> 'a

val error_assumption : env -> unsafe_judgment -> 'a

val error_reference_variables : env -> Id.t -> constr -> 'a

val error_elim_arity :
  env -> pinductive -> Sorts.family list -> constr -> unsafe_judgment ->
      (Sorts.family * Sorts.family * arity_error) option -> 'a

val error_case_not_inductive : env -> unsafe_judgment -> 'a

val error_number_branches : env -> unsafe_judgment -> int -> 'a

val error_ill_formed_branch : env -> constr -> pconstructor -> constr -> constr -> 'a

val error_generalization : env -> Name.t * types -> unsafe_judgment -> 'a

val error_actual_type : env -> unsafe_judgment -> types -> 'a

val error_cant_apply_not_functional :
  env -> unsafe_judgment -> unsafe_judgment array -> 'a

val error_cant_apply_bad_type :
  env -> int * constr * constr ->
      unsafe_judgment -> unsafe_judgment array -> 'a

val error_ill_formed_rec_body :
  env -> guard_error -> Name.t array -> int -> env -> unsafe_judgment array -> 'a

val error_ill_typed_rec_body  :
  env -> int -> Name.t array -> unsafe_judgment array -> types array -> 'a

val error_elim_explain : Sorts.family -> Sorts.family -> arity_error

val error_unsatisfied_constraints : env -> Univ.Constraint.t -> 'a

val error_undeclared_universe : env -> Univ.Level.t -> 'a
