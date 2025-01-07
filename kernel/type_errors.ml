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

(* Type errors. *)

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
  | IllFormedRecBody of 'constr pguard_error * (Name.t, 'r) Context.pbinder_annot array * int * env * ('constr, 'types) punsafe_judgment array
  | IllTypedRecBody of
      int * (Name.t, 'r) Context.pbinder_annot array * ('constr, 'types) punsafe_judgment array * 'types array
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

exception InductiveError of env * inductive_error

let error_unbound_rel env n =
  raise (TypeError (env, UnboundRel n))

let error_unbound_var env v =
  raise (TypeError (env, UnboundVar v))

let error_not_type env j =
  raise (TypeError (env, NotAType j))

let error_assumption env j =
  raise (TypeError (env, BadAssumption j))

let error_reference_variables env id c =
  raise (TypeError (env, ReferenceVariables (id,c)))

let error_elim_arity env ind c okinds =
  raise (TypeError (env, ElimArity (ind, c, okinds)))

let error_case_not_inductive env j =
  raise (TypeError (env, CaseNotInductive j))

let error_case_on_private_ind env ind =
  raise (TypeError (env, CaseOnPrivateInd ind))

let error_number_branches env cj expn =
  raise (TypeError (env, NumberBranches (cj, expn)))

let error_ill_formed_branch env c i actty expty =
  raise (TypeError (env, IllFormedBranch (c, i, actty, expty)))

let error_generalization env nvar c =
  raise (TypeError (env, Generalization (nvar,c)))

let error_actual_type env j expty =
  raise (TypeError (env, ActualType (j,expty)))

let error_incorrect_primitive env p t =
  raise (TypeError (env, IncorrectPrimitive (p, t)))

let error_cant_apply_not_functional env rator randl =
  raise (TypeError (env, CantApplyNonFunctional (rator,randl)))

let error_cant_apply_bad_type env t rator randl =
  raise (TypeError (env, CantApplyBadType (t,rator,randl)))

let error_ill_formed_rec_body env why lna i fixenv vdefj =
  raise (TypeError (env, IllFormedRecBody (why,lna,i,fixenv,vdefj)))

let error_ill_typed_rec_body env i lna vdefj vargs =
  raise (TypeError (env, IllTypedRecBody (i,lna,vdefj,vargs)))

let error_unsatisfied_qconstraints env c =
  raise (TypeError (env, UnsatisfiedQConstraints c))

let error_unsatisfied_constraints env c =
  raise (TypeError (env, UnsatisfiedConstraints c))

let error_undeclared_qualities env l =
  raise (TypeError (env, UndeclaredQualities l))

let error_undeclared_universes env l =
  raise (TypeError (env, UndeclaredUniverses l))

let error_disallowed_sprop env =
  raise (TypeError (env, DisallowedSProp))

let error_bad_binder_relevance env rlv decl =
  raise (TypeError (env, BadBinderRelevance (rlv, decl)))

let error_bad_case_relevance env rlv case =
  raise (TypeError (env, BadCaseRelevance (rlv, mkCase case)))

let error_bad_invert env =
  raise (TypeError (env, BadInvert))

let error_bad_variance env ~lev ~expected ~actual =
  raise (TypeError (env, BadVariance {lev;expected;actual}))

let error_undeclared_used_variables env ~declared_vars ~inferred_vars =
  raise (TypeError (env, UndeclaredUsedVariables {declared_vars; inferred_vars}))

let map_pfix_guard_error f = function
| NotEnoughAbstractionInFixBody -> NotEnoughAbstractionInFixBody
| RecursionNotOnInductiveType c -> RecursionNotOnInductiveType (f c)
| RecursionOnIllegalTerm (n, (env, c), l1_l2) -> RecursionOnIllegalTerm (n, (env, f c), l1_l2)
| NotEnoughArgumentsForFixCall n -> NotEnoughArgumentsForFixCall n
| FixpointOnIrrelevantInductive -> FixpointOnIrrelevantInductive

let map_pcofix_guard_error f = function
| CodomainNotInductiveType c -> CodomainNotInductiveType (f c)
| NestedRecursiveOccurrences -> NestedRecursiveOccurrences
| UnguardedRecursiveCall c -> UnguardedRecursiveCall (f c)
| RecCallInTypeOfAbstraction c -> RecCallInTypeOfAbstraction (f c)
| RecCallInNonRecArgOfConstructor c -> RecCallInNonRecArgOfConstructor (f c)
| RecCallInTypeOfDef c -> RecCallInTypeOfDef (f c)
| RecCallInCaseFun c -> RecCallInCaseFun (f c)
| RecCallInCaseArg c -> RecCallInCaseArg (f c)
| RecCallInCasePred c -> RecCallInCasePred (f c)
| NotGuardedForm c -> NotGuardedForm (f c)
| ReturnPredicateNotCoInductive c -> ReturnPredicateNotCoInductive (f c)

let map_pguard_error f = function
| FixGuardError e -> FixGuardError (map_pfix_guard_error f e)
| CoFixGuardError e -> CoFixGuardError (map_pcofix_guard_error f e)

let map_ptype_error fr f = function
| UnboundRel _ | UnboundVar _ | CaseOnPrivateInd _ | IllFormedCaseParams
| UndeclaredQualities _ | UndeclaredUniverses _ | DisallowedSProp
| UnsatisfiedQConstraints _ | UnsatisfiedConstraints _
| ReferenceVariables _ | BadInvert | BadVariance _ | UndeclaredUsedVariables _ as e -> e
| NotAType j -> NotAType (on_judgment f j)
| BadAssumption j -> BadAssumption (on_judgment f j)
| ElimArity (pi, c, ar) -> ElimArity (pi, f c, ar)
| CaseNotInductive j -> CaseNotInductive (on_judgment f j)
| WrongCaseInfo (pi, ci) -> WrongCaseInfo (pi, ci)
| NumberBranches (j, n) -> NumberBranches (on_judgment f j, n)
| IllFormedBranch (c, pc, t1, t2) -> IllFormedBranch (f c, pc, f t1, f t2)
| Generalization ((na, t), j) -> Generalization ((na, f t), on_judgment f j)
| ActualType (j, t) -> ActualType (on_judgment f j, f t)
| IncorrectPrimitive (p, t) -> IncorrectPrimitive ({p with uj_type=f p.uj_type}, f t)
| CantApplyBadType ((n, c1, c2), j, vj) ->
  CantApplyBadType ((n, f c1, f c2), on_judgment f j, Array.map (on_judgment f) vj)
| CantApplyNonFunctional (j, jv) -> CantApplyNonFunctional (on_judgment f j, Array.map (on_judgment f) jv)
| IllFormedRecBody (ge, na, n, env, jv) ->
  IllFormedRecBody (map_pguard_error f ge, Array.map (Context.map_annot_relevance_het fr) na, n, env, Array.map (on_judgment f) jv)
| IllTypedRecBody (n, na, jv, t) ->
  IllTypedRecBody (n, Array.map (Context.map_annot_relevance_het fr) na, Array.map (on_judgment f) jv, Array.map f t)
| BadBinderRelevance (rlv, decl) -> BadBinderRelevance (fr rlv, Context.Rel.Declaration.map_constr_het fr f decl)
| BadCaseRelevance (rlv, case) -> BadCaseRelevance (fr rlv, f case)
