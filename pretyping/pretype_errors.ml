
(* $Id$ *)

open Names
open Sign
open Environ
open Type_errors
open Rawterm

exception PretypeError of loc * path_kind * context * type_error

let error_cant_find_case_type_loc loc env expr =
  raise (PretypeError (loc,CCI,context env,CantFindCaseType expr))

let error_ill_formed_branch k env c i actty expty =
  raise (TypeError (k, context env, IllFormedBranch (c,i,actty,expty)))

let error_number_branches_loc loc k env c ct expn =
  raise (PretypeError (loc, k, context env, NumberBranches (c,ct,expn)))

let error_case_not_inductive_loc loc k env c ct =
  raise (PretypeError (loc, k, context env, CaseNotInductive (c,ct)))

(* Pattern-matching errors *)

let error_bad_constructor_loc loc k cstr ind =
  raise (PretypeError (loc, k, Global.context(), BadConstructor (cstr,ind)))

let error_wrong_numarg_constructor_loc loc k c n =
  raise (PretypeError (loc, k, Global.context(), WrongNumargConstructor (c,n)))

let error_wrong_predicate_arity_loc loc k env c n1 n2 =
  raise (PretypeError (loc, k, context env, WrongPredicateArity (c,n1,n2)))

let error_needs_inversion k env x t =
  raise (TypeError (k, context env, NeedsInversion (x,t)))


let error_ill_formed_branch_loc loc k env c i actty expty =
  raise (PretypeError (loc, k, context env, IllFormedBranch (c,i,actty,expty)))

let error_occur_check k env ev c =
  raise (TypeError (k, context env, OccurCheck (ev,c)))

let error_not_clean k env ev c =
  raise (TypeError (k, context env, NotClean (ev,c)))

