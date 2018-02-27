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
open Cic
open Environ

type unsafe_judgment = constr * constr

let nf_betaiota c = c

(* Type errors. *)

type guard_error =
  (* Fixpoints *)
  | NotEnoughAbstractionInFixBody
  | RecursionNotOnInductiveType of constr
  | RecursionOnIllegalTerm of int * (env * constr) * int list * int list
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
  | ReturnPredicateNotCoInductive of constr

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
  | ElimArity of pinductive * sorts_family list * constr * unsafe_judgment
      * (sorts_family * sorts_family * arity_error) option
  | CaseNotInductive of unsafe_judgment
  | WrongCaseInfo of inductive * case_info
  | NumberBranches of unsafe_judgment * int
  | IllFormedBranch of constr * int * constr * constr
  | Generalization of (Name.t * constr) * unsafe_judgment
  | ActualType of unsafe_judgment * constr
  | CantApplyBadType of
      (int * constr * constr) * unsafe_judgment * unsafe_judgment array
  | CantApplyNonFunctional of unsafe_judgment * unsafe_judgment array
  | IllFormedRecBody of guard_error * Name.t array * int
  | IllTypedRecBody of
      int * Name.t array * unsafe_judgment array * constr array
  | UnsatisfiedConstraints of Univ.constraints

exception TypeError of env * type_error

let nfj (c,ct) = (c, nf_betaiota ct)

let error_unbound_rel env n =
  raise (TypeError (env, UnboundRel n))

let error_unbound_var env v =
  raise (TypeError (env, UnboundVar v))

let error_not_type env j =
  raise (TypeError (env, NotAType j))

let error_assumption env j =
  raise (TypeError (env, BadAssumption j))

let error_reference_variables env id =
  raise (TypeError (env, ReferenceVariables id))

let error_elim_arity env ind aritylst c pj okinds =
  raise (TypeError (env, ElimArity (ind,aritylst,c,pj,okinds)))

let error_case_not_inductive env j =
  raise (TypeError (env, CaseNotInductive j))

let error_number_branches env cj expn =
  raise (TypeError (env, NumberBranches (nfj cj,expn)))

let error_ill_formed_branch env c i actty expty =
  raise (TypeError (env,
    IllFormedBranch (c,i,nf_betaiota actty, nf_betaiota expty)))

let error_actual_type env j expty =
  raise (TypeError (env, ActualType (j,expty)))

let error_cant_apply_not_functional env rator randl =
  raise (TypeError (env, CantApplyNonFunctional (rator,randl)))

let error_cant_apply_bad_type env t rator randl =
  raise (TypeError (env, CantApplyBadType (t,rator,randl)))

let error_ill_formed_rec_body env why lna i =
  raise (TypeError (env, IllFormedRecBody (why,lna,i)))

let error_ill_typed_rec_body env i lna vdefj vargs =
  raise (TypeError (env, IllTypedRecBody (i,lna,vdefj,vargs)))

let error_unsatisfied_constraints env c =
  raise (TypeError (env, UnsatisfiedConstraints c))
