
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

let error_ill_formed_branch_loc loc k env c i actty expty =
  raise (PretypeError (loc, k, context env, IllFormedBranch (c,i,actty,expty)))

let error_occur_check k env ev c =
  raise (TypeError (k, context env, OccurCheck (ev,c)))

let error_not_clean k env ev c =
  raise (TypeError (k, context env, NotClean (ev,c)))

