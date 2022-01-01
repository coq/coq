(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Environ
open Univ

(** Type errors. {% \label{typeerrors} %} *)

(*i Rem: NotEnoughAbstractionInFixBody should only occur with "/i" Fix
    notation i*)
type 'constr pfix_guard_error =
  (* Fixpoints *)
  | NotEnoughAbstractionInFixBody
  | RecursionNotOnInductiveType of 'constr
  | RecursionOnIllegalTerm of int * (env * 'constr) * (int list * int list) Lazy.t
  | NotEnoughArgumentsForFixCall of int
  | FixpointOnIrrelevantInductive

type 'constr pcofix_guard_error =
  (* CoFixpoints *)
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

type 'constr pguard_error =
  | FixGuardError of 'constr pfix_guard_error
  | CoFixGuardError of 'constr pcofix_guard_error

type fix_guard_error = constr pfix_guard_error
type cofix_guard_error = constr pcofix_guard_error
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
  | ReferenceVariables of Id.t * GlobRef.t
  | ElimArity of pinductive * 'constr * ('constr, 'types) punsafe_judgment
      * (Sorts.family * Sorts.family * Sorts.family * arity_error) option
  | CaseNotInductive of ('constr, 'types) punsafe_judgment
  | WrongCaseInfo of pinductive * case_info
  | NumberBranches of ('constr, 'types) punsafe_judgment * int
  | IllFormedBranch of 'constr * pconstructor * 'constr * 'constr
  | Generalization of (Name.t * 'types) * ('constr, 'types) punsafe_judgment
  | ActualType of ('constr, 'types) punsafe_judgment * 'types
  | IncorrectPrimitive of (CPrimitives.op_or_type,'types) punsafe_judgment * 'types
  | CantApplyBadType of
      (int * 'constr * 'constr) * ('constr, 'types) punsafe_judgment * ('constr, 'types) punsafe_judgment array
  | CantApplyNonFunctional of ('constr, 'types) punsafe_judgment * ('constr, 'types) punsafe_judgment array
  | IllFormedRecBody of 'constr pguard_error * Name.t Context.binder_annot array * int * env * ('constr, 'types) punsafe_judgment array
  | IllTypedRecBody of
      int * Name.t Context.binder_annot array * ('constr, 'types) punsafe_judgment array * 'types array
  | UnsatisfiedConstraints of Constraints.t
  | UndeclaredUniverse of Level.t
  | DisallowedSProp
  | BadRelevance
  | BadInvert
  | BadVariance of { lev : Level.t; expected : Variance.t; actual : Variance.t }

type type_error = (constr, types) ptype_error

exception TypeError of env * type_error

(** The different kinds of errors that may result of a malformed inductive
    definition. *)
type inductive_error =
  | NonPos of env * constr * constr
  | NotEnoughArgs of env * constr * constr
  | NotConstructor of env * Id.t * constr * constr * int * int
  | NonPar of env * constr * int * constr * constr
  | SameNamesTypes of Id.t
  | SameNamesConstructors of Id.t
  | SameNamesOverlap of Id.t list
  | NotAnArity of env * constr
  | BadEntry
  | LargeNonPropInductiveNotInType
  | MissingConstraints of (Sorts.t list * Sorts.t)
  (* each universe in the set should have been <= the other one *)

exception InductiveError of inductive_error

(** Raising functions *)

val error_unbound_rel : env -> int -> 'a

val error_unbound_var : env -> variable -> 'a

val error_not_type : env -> unsafe_judgment -> 'a

val error_assumption : env -> unsafe_judgment -> 'a

val error_reference_variables : env -> Id.t -> GlobRef.t -> 'a

val error_elim_arity :
  env -> pinductive -> constr -> unsafe_judgment ->
      (Sorts.family * Sorts.family * Sorts.family * arity_error) option -> 'a

val error_case_not_inductive : env -> unsafe_judgment -> 'a

val error_number_branches : env -> unsafe_judgment -> int -> 'a

val error_ill_formed_branch : env -> constr -> pconstructor -> constr -> constr -> 'a

val error_generalization : env -> Name.t * types -> unsafe_judgment -> 'a

val error_actual_type : env -> unsafe_judgment -> types -> 'a

val error_incorrect_primitive : env -> (CPrimitives.op_or_type,types) punsafe_judgment -> types -> 'a

val error_cant_apply_not_functional :
  env -> unsafe_judgment -> unsafe_judgment array -> 'a

val error_cant_apply_bad_type :
  env -> int * constr * constr ->
      unsafe_judgment -> unsafe_judgment array -> 'a

val error_ill_formed_rec_body :
  env -> guard_error -> Name.t Context.binder_annot array -> int -> env -> unsafe_judgment array -> 'a

val error_ill_typed_rec_body  :
  env -> int -> Name.t Context.binder_annot array -> unsafe_judgment array -> types array -> 'a

val error_elim_explain : Sorts.family -> Sorts.family -> arity_error

val error_unsatisfied_constraints : env -> Constraints.t -> 'a

val error_undeclared_universe : env -> Level.t -> 'a

val error_disallowed_sprop : env -> 'a

val error_bad_relevance : env -> 'a

val error_bad_invert : env -> 'a

val error_bad_variance : env -> lev:Level.t -> expected:Variance.t -> actual:Variance.t -> 'a

val map_pguard_error : ('c -> 'd) -> 'c pguard_error -> 'd pguard_error
val map_ptype_error : ('c -> 'd) -> ('c, 'c) ptype_error -> ('d, 'd) ptype_error
