
(* $Id$ *)

open Names
open Sign
open Term
open Environ
open Type_errors
open Rawterm

type ml_case_error =
  | MlCaseAbsurd
  | MlCaseDependent

type pretype_error =
  (* Old Case *)
  | MlCase of ml_case_error
  | CantFindCaseType of constr
  (* Unification *)
  | OccurCheck of int * constr
  | NotClean of int * constr
  (* Pretyping *)
  | VarNotFound of identifier
  | UnexpectedType of constr * constr
  | NotProduct of constr

exception PretypeError of env * pretype_error

let raise_pretype_error (loc,ctx,te) =
  Stdpp.raise_with_loc loc (PretypeError(ctx,te))

let raise_located_type_error (loc,k,ctx,te) =
  Stdpp.raise_with_loc loc (TypeError(k,ctx,te))

let error_cant_find_case_type_loc loc env expr =
  raise_pretype_error (loc, env, CantFindCaseType expr)

let error_ill_formed_branch_loc loc k env c i actty expty =
  raise_located_type_error (loc, k, env, IllFormedBranch (c,i,actty,expty))

let error_actual_type_loc loc env c actty expty =
  raise_located_type_error (loc, CCI, env, ActualType (c,actty,expty))

let error_cant_apply_not_functional_loc loc env rator randl =
  raise_located_type_error
    (loc,CCI,env, CantApplyNonFunctional (rator,randl))

let error_cant_apply_bad_type_loc loc env t rator randl =
  raise_located_type_error (loc, CCI, env, CantApplyBadType (t,rator,randl))

let error_ill_formed_branch k env c i actty expty =
  raise (TypeError (k, env, IllFormedBranch (c,i,actty,expty)))

let error_number_branches_loc loc k env c ct expn =
  raise_located_type_error (loc, k, env, NumberBranches (c,ct,expn))

let error_case_not_inductive_loc loc k env c ct =
  raise_located_type_error (loc, k, env, CaseNotInductive (c,ct))


(*s Implicit arguments synthesis errors *)

let error_occur_check env ev c =
  raise (PretypeError (env, OccurCheck (ev,c)))

let error_not_clean env ev c =
  raise (PretypeError (env, NotClean (ev,c)))

(*s Ml Case errors *)

let error_ml_case_loc loc env mes =
  raise_pretype_error (loc, env, MlCase mes)

(*s Pretyping errors *)

let error_var_not_found_loc loc s =
  raise_pretype_error (loc, Global.env() (*bidon*), VarNotFound s)

let error_unexpected_type_loc loc env actty expty =
  raise_pretype_error (loc, env, UnexpectedType (actty, expty))

let error_not_product_loc loc env c =
  raise_pretype_error (loc, env, NotProduct c)
