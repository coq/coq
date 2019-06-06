(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Environ
open Reduction

(* Type errors. *)

type 'constr pguard_error =
  (* Fixpoints *)
  | NotEnoughAbstractionInFixBody
  | RecursionNotOnInductiveType of 'constr
  | RecursionOnIllegalTerm of int * (env * 'constr) * int list * int list
  | NotEnoughArgumentsForFixCall of int
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
  | FixpointOnIrrelevantInductive

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
  | UnsatisfiedConstraints of Univ.Constraint.t
  | UndeclaredUniverse of Univ.Level.t
  | DisallowedSProp
  | BadRelevance

type type_error = (constr, types) ptype_error

exception TypeError of env * type_error

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
  | BadUnivs

exception InductiveError of inductive_error

let nfj env {uj_val=c;uj_type=ct} =
  {uj_val=c;uj_type=nf_betaiota env ct}

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

let error_elim_arity env ind c pj okinds =
  raise (TypeError (env, ElimArity (ind,c,pj,okinds)))

let error_case_not_inductive env j =
  raise (TypeError (env, CaseNotInductive j))

let error_number_branches env cj expn =
  raise (TypeError (env, NumberBranches (nfj env cj,expn)))

let error_ill_formed_branch env c i actty expty =
  raise (TypeError (env,
    IllFormedBranch (c,i,nf_betaiota env actty, nf_betaiota env expty)))

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

let error_elim_explain kp ki =
  let open Sorts in
  match kp,ki with
  | (InType | InSet), InProp -> NonInformativeToInformative
  | InType, InSet -> StrongEliminationOnNonSmallType (* if Set impredicative *)
  | _ -> WrongArity

let error_unsatisfied_constraints env c =
  raise (TypeError (env, UnsatisfiedConstraints c))

let error_undeclared_universe env l =
  raise (TypeError (env, UndeclaredUniverse l))

let error_disallowed_sprop env =
  raise (TypeError (env, DisallowedSProp))

let error_bad_relevance env =
  raise (TypeError (env, BadRelevance))

let map_pguard_error f = function
| NotEnoughAbstractionInFixBody -> NotEnoughAbstractionInFixBody
| RecursionNotOnInductiveType c -> RecursionNotOnInductiveType (f c)
| RecursionOnIllegalTerm (n, (env, c), l1, l2) -> RecursionOnIllegalTerm (n, (env, f c), l1, l2)
| NotEnoughArgumentsForFixCall n -> NotEnoughArgumentsForFixCall n
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
| FixpointOnIrrelevantInductive -> FixpointOnIrrelevantInductive

let map_ptype_error f = function
| UnboundRel n -> UnboundRel n
| UnboundVar id -> UnboundVar id
| NotAType j -> NotAType (on_judgment f j)
| BadAssumption j -> BadAssumption (on_judgment f j)
| ReferenceVariables (id, c) -> ReferenceVariables (id, f c)
| ElimArity (pi, c, j, ar) -> ElimArity (pi, f c, on_judgment f j, ar)
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
  IllFormedRecBody (map_pguard_error f ge, na, n, env, Array.map (on_judgment f) jv)
| IllTypedRecBody (n, na, jv, t) ->
  IllTypedRecBody (n, na, Array.map (on_judgment f) jv, Array.map f t)
| UnsatisfiedConstraints g -> UnsatisfiedConstraints g
| UndeclaredUniverse l -> UndeclaredUniverse l
| DisallowedSProp -> DisallowedSProp
| BadRelevance -> BadRelevance
