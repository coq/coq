(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
open UVars

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

type ('constr, 'types) pcant_apply_bad_type =
  (int * 'constr * 'constr) * ('constr, 'types) punsafe_judgment * ('constr, 'types) punsafe_judgment array

type ('constr, 'types, 'r) ptype_error =
  | UnboundRel of int
  | UnboundVar of variable
  | NotAType of ('constr, 'types) punsafe_judgment
  | BadAssumption of ('constr, 'types) punsafe_judgment
  | ReferenceVariables of Id.t * GlobRef.t
  | ElimArity of pinductive * 'constr * Sorts.t option
  | CaseNotInductive of ('constr, 'types) punsafe_judgment
  | CaseOnPrivateInd of inductive
  | WrongCaseInfo of pinductive * case_info
  | NumberBranches of ('constr, 'types) punsafe_judgment * int
  | IllFormedCaseParams
  | IllFormedBranch of 'constr * pconstructor * 'constr * 'constr
  | Generalization of (Name.t * 'types) * ('constr, 'types) punsafe_judgment
  | ActualType of ('constr, 'types) punsafe_judgment * 'types
  | IncorrectPrimitive of (CPrimitives.op_or_type,'types) punsafe_judgment * 'types
  | CantApplyBadType of ('constr, 'types) pcant_apply_bad_type
  | CantApplyNonFunctional of ('constr, 'types) punsafe_judgment * ('constr, 'types) punsafe_judgment array
  | IllFormedRecBody of 'constr pguard_error * (Name.t,'r) Context.pbinder_annot array * int * env * ('constr, 'types) punsafe_judgment array
  | IllTypedRecBody of
      int * (Name.t,'r) Context.pbinder_annot array * ('constr, 'types) punsafe_judgment array * 'types array
  | UnsatisfiedQConstraints of Sorts.QConstraints.t
  | UnsatisfiedConstraints of Constraints.t
  | UndeclaredQualities of Sorts.QVar.Set.t
  | UndeclaredUniverses of Level.Set.t
  | DisallowedSProp
  | BadBinderRelevance of 'r * ('constr, 'types, 'r) Context.Rel.Declaration.pt
  | BadCaseRelevance of 'r * 'constr
  | BadInvert
  | BadVariance of { lev : Level.t; expected : Variance.t; actual : Variance.t }
  | UndeclaredUsedVariables of { declared_vars : Id.Set.t; inferred_vars : Id.Set.t }

type type_error = (constr, types, Sorts.relevance) ptype_error

exception TypeError of env * type_error

(** The different kinds of errors that may result of a malformed inductive
    definition. *)
type inductive_error =
  | NonPos of constr * constr
  | NotEnoughArgs of constr * constr
  | NotConstructor of Id.t * constr * constr * int * int
  | NonPar of constr * int * constr * constr
  | SameNamesTypes of Id.t
  | SameNamesConstructors of Id.t
  | SameNamesOverlap of Id.t list
  | NotAnArity of constr
  | BadEntry
  | LargeNonPropInductiveNotInType
  | MissingConstraints of (Sorts.t list * Sorts.t)
  (* each universe in the set should have been <= the other one *)

exception InductiveError of env * inductive_error

(** Raising functions *)

val error_unbound_rel : env -> int -> 'a

val error_unbound_var : env -> variable -> 'a

val error_not_type : env -> unsafe_judgment -> 'a

val error_assumption : env -> unsafe_judgment -> 'a

val error_reference_variables : env -> Id.t -> GlobRef.t -> 'a

val error_elim_arity :
  env -> pinductive -> constr -> Sorts.t option -> 'a

val error_case_not_inductive : env -> unsafe_judgment -> 'a

val error_case_on_private_ind : env -> inductive -> 'a

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
  env -> guard_error -> Name.t binder_annot array -> int -> env -> unsafe_judgment array -> 'a

val error_ill_typed_rec_body  :
  env -> int -> Name.t binder_annot array -> unsafe_judgment array -> types array -> 'a

val error_unsatisfied_qconstraints : env -> Sorts.QConstraints.t -> 'a

val error_unsatisfied_constraints : env -> Constraints.t -> 'a

val error_undeclared_qualities : env -> Sorts.QVar.Set.t -> 'a

val error_undeclared_universes : env -> Level.Set.t -> 'a

val error_disallowed_sprop : env -> 'a

val error_bad_binder_relevance : env -> Sorts.relevance -> rel_declaration -> 'a

val error_bad_case_relevance : env -> Sorts.relevance -> Constr.case -> 'a

val error_bad_invert : env -> 'a

val error_bad_variance : env -> lev:Level.t -> expected:Variance.t -> actual:Variance.t -> 'a

val error_undeclared_used_variables : env -> declared_vars:Id.Set.t -> inferred_vars:Id.Set.t -> 'a

val map_pguard_error : ('c -> 'd) -> 'c pguard_error -> 'd pguard_error
val map_ptype_error : ('r1 -> 'r2) -> ('c -> 'd) -> ('c, 'c, 'r1) ptype_error -> ('d, 'd, 'r2) ptype_error
