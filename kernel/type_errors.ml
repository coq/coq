
(* $Id$ *)

open Pp
open Names
open Term
open Sign
open Environ

(* Type errors. *)

type type_error =
  | UnboundRel of int
  | CantExecute of constr
  | NotAType of constr
  | BadAssumption of constr
  | ReferenceVariables of identifier
  | ElimArity of inductive * constr list * constr * constr * constr
      * (constr * constr * string) option
  | CaseNotInductive of constr * constr
  | NumberBranches of constr * constr * int
  | IllFormedBranch of constr * int * constr * constr
  | Generalization of (name * typed_type) * constr
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
  (* Pattern-matching errors *)
  | BadConstructor of constructor * inductive
  | WrongNumargConstructor of constructor_path * int
  | WrongPredicateArity of constr * int * int
  | NeedsInversion of constr * constr

exception TypeError of path_kind * context * type_error

let error_unbound_rel k env n =
  raise (TypeError (k, context env, UnboundRel n))

let error_cant_execute k env c =
  raise (TypeError (k, context env, CantExecute c))

let error_not_type k env c =
  raise (TypeError (k, context env, NotAType c))

let error_assumption k env c =
  raise (TypeError (k, context env, BadAssumption c))

let error_reference_variables k env id =
  raise (TypeError (k, context env, ReferenceVariables id))

let error_elim_arity k env ind aritylst c p pt okinds = 
  raise (TypeError (k, context env, ElimArity (ind,aritylst,c,p,pt,okinds)))

let error_case_not_inductive k env c ct = 
  raise (TypeError (k, context env, CaseNotInductive (c,ct)))

let error_number_branches k env c ct expn =
  raise (TypeError (k, context env, NumberBranches (c,ct,expn)))

let error_ill_formed_branch k env c i actty expty =
  raise (TypeError (k, context env, IllFormedBranch (c,i,actty,expty)))

let error_generalization k env nvar c =
  raise (TypeError (k, context env, Generalization (nvar,c)))

let error_actual_type k env c actty expty =
  raise (TypeError (k, context env, ActualType (c,actty,expty)))

let error_cant_apply_not_functional k env rator randl =
  raise (TypeError (k, context env, CantApplyNonFunctional (rator,randl)))

let error_cant_apply_bad_type k env t rator randl =
  raise (TypeError (k, context env, CantApplyBadType (t,rator,randl)))

let error_ill_formed_rec_body k env str lna i vdefs =
  raise (TypeError (k, context env, IllFormedRecBody (str,lna,i,vdefs)))

let error_ill_typed_rec_body k env i lna vdefj vargs =
  raise (TypeError (k, context env, IllTypedRecBody (i,lna,vdefj,vargs)))

let error_not_inductive k env c =
  raise (TypeError (k, context env, NotInductive c))

let error_ml_case k env mes c ct br brt =
  raise (TypeError (k, context env, MLCase (mes,c,ct,br,brt)))
