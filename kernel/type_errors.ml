(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Names
open Term
open Sign
open Environ
open Reduction

(* Type errors. *)

type guard_error =
  (* Fixpoints *)
  | NotEnoughAbstractionInFixBody
  | RecursionNotOnInductiveType
  | RecursionOnIllegalTerm
  | NotEnoughArgumentsForFixCall
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

type type_error =
  | UnboundRel of int
  | NotAType of unsafe_judgment
  | BadAssumption of constr
  | ReferenceVariables of identifier
  | ElimArity of inductive * constr list * constr * unsafe_judgment
      * (constr * constr * string) option
  | CaseNotInductive of unsafe_judgment
  | NumberBranches of unsafe_judgment * int
  | IllFormedBranch of constr * int * constr * constr
  | Generalization of (name * types) * unsafe_judgment
  | ActualType of constr * constr * constr
  | CantApplyBadType of (int * constr * constr)
      * unsafe_judgment * unsafe_judgment list
  | CantApplyNonFunctional of unsafe_judgment * unsafe_judgment list
  | IllFormedRecBody of guard_error * name array * int * constr array
  | IllTypedRecBody of int * name array * unsafe_judgment array 
      * types array

exception TypeError of path_kind * env * type_error

let nfj {uj_val=c;uj_type=ct} =
  {uj_val=c;uj_type=nf_betaiota ct}

let error_unbound_rel k env n =
  raise (TypeError (k, env, UnboundRel n))

let error_not_type k env c =
  raise (TypeError (k, env, NotAType c))

let error_assumption k env c =
  raise (TypeError (k, env, BadAssumption c))

let error_reference_variables k env id =
  raise (TypeError (k, env, ReferenceVariables id))

let error_elim_arity k env ind aritylst c pj okinds = 
  raise (TypeError (k, env, ElimArity (ind,aritylst,c,pj,okinds)))

let error_case_not_inductive k env j = 
  raise (TypeError (k, env, CaseNotInductive j))

let error_number_branches k env cj expn =
  raise (TypeError (k, env, NumberBranches (nfj cj,expn)))

let error_ill_formed_branch k env c i actty expty =
  raise (TypeError (k, env,
    IllFormedBranch (c,i,nf_betaiota actty, nf_betaiota expty)))

let error_generalization k env nvar c =
  raise (TypeError (k, env, Generalization (nvar,c)))

let error_actual_type k env c actty expty =
  raise (TypeError (k, env, ActualType (c,actty,expty)))

let error_cant_apply_not_functional k env rator randl =
  raise (TypeError (k, env, CantApplyNonFunctional (rator,randl)))

let error_cant_apply_bad_type k env t rator randl =
  raise(TypeError (k, env, CantApplyBadType (t,rator,randl)))

let error_ill_formed_rec_body k env why lna i vdefs =
  raise (TypeError (k, env, IllFormedRecBody (why,lna,i,vdefs)))

let error_ill_typed_rec_body k env i lna vdefj vargs =
  raise (TypeError (k, env, IllTypedRecBody (i,lna,vdefj,vargs)))


