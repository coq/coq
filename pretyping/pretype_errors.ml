(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Identifier
open Names
open Sign
open Term
open Environ
open Type_errors
open Rawterm
open Inductive

type ml_case_error =
  | MlCaseAbsurd
  | MlCaseDependent

type pretype_error =
  (* Old Case *)
  | MlCase of ml_case_error * inductive_type * unsafe_judgment
  | CantFindCaseType of constr
  (* Unification *)
  | OccurCheck of int * constr
  | NotClean of int * constr
  (* Pretyping *)
  | VarNotFound of identifier
  | UnexpectedType of constr * constr
  | NotProduct of constr

exception PretypeError of env * pretype_error

(* Replacing defined evars for error messages *)
let rec whd_evar sigma c =
  match kind_of_term c with
    | IsEvar (ev,args) when Evd.in_dom sigma ev & Evd.is_defined sigma ev ->
	whd_evar sigma (Instantiate.existential_value sigma (ev,args))
    | _ -> collapse_appl c

let nf_evar sigma = Reduction.local_strong (whd_evar sigma)
let j_nf_evar sigma j = 
  { uj_val = nf_evar sigma j.uj_val;
    uj_type = nf_evar sigma j.uj_type }
let jl_nf_evar sigma jl = List.map (j_nf_evar sigma) jl
let jv_nf_evar sigma = Array.map (j_nf_evar sigma)
let tj_nf_evar sigma {utj_val=v;utj_type=t} =
  {utj_val=type_app (nf_evar sigma) v;utj_type=t}


let env_ise sigma env =
  map_context (nf_evar sigma) env


let raise_pretype_error (loc,ctx,sigma,te) =
  Stdpp.raise_with_loc loc (PretypeError(env_ise sigma ctx,te))

let raise_located_type_error (loc,ctx,sigma,te) =
  Stdpp.raise_with_loc loc (TypeError(env_ise sigma ctx,te))


let error_actual_type_loc loc env sigma {uj_val=c;uj_type=actty} expty =
  raise_located_type_error
    (loc, env, sigma,
     ActualType (c,nf_evar sigma actty, nf_evar sigma expty))

let error_cant_apply_not_functional_loc loc env sigma rator randl =
  raise_located_type_error
    (loc, env, sigma,
    CantApplyNonFunctional (j_nf_evar sigma rator, jl_nf_evar sigma randl))

let error_cant_apply_bad_type_loc loc env sigma (n,c,t) rator randl =
  raise_located_type_error
    (loc, env, sigma,
     CantApplyBadType
       ((n,nf_evar sigma c, nf_evar sigma t),
        j_nf_evar sigma rator, jl_nf_evar sigma randl))

let error_cant_find_case_type_loc loc env sigma expr =
  raise_pretype_error
    (loc, env, sigma, CantFindCaseType (nf_evar sigma expr))

let error_ill_formed_branch_loc loc env sigma c i actty expty =
  let simp t = Reduction.nf_betaiota (nf_evar sigma t) in
  raise_located_type_error
    (loc, env, sigma,
     IllFormedBranch (nf_evar sigma c,i,simp actty, simp expty))

let error_number_branches_loc loc env sigma cj expn =
  raise_located_type_error
    (loc, env, sigma,
     NumberBranches (j_nf_evar sigma cj, expn))

let error_case_not_inductive_loc loc env sigma cj =
  raise_located_type_error
    (loc, env, sigma, CaseNotInductive (j_nf_evar sigma cj))

let error_ill_typed_rec_body_loc loc env sigma i na jl tys =
  raise_located_type_error
    (loc, env, sigma,
     IllTypedRecBody (i,na,jv_nf_evar sigma jl,
                      Array.map (nf_evar sigma) tys))

(*s Implicit arguments synthesis errors. It is hard to find
    a precise location. *)

let error_occur_check env sigma ev c =
  let c = nf_evar sigma c in
  raise (PretypeError (env_ise sigma env, OccurCheck (ev,c)))

let error_not_clean env sigma ev c =
  let c = nf_evar sigma c in
  raise (PretypeError (env_ise sigma env, NotClean (ev,c)))

(*s Ml Case errors *)

let error_ml_case_loc loc env sigma mes indt j =
  raise_pretype_error
    (loc, env, sigma, MlCase (mes, indt, j_nf_evar sigma j))

(*s Pretyping errors *)

let error_unexpected_type_loc loc env sigma actty expty =
  raise_pretype_error
    (loc, env, sigma,
     UnexpectedType (nf_evar sigma actty, nf_evar sigma expty))

let error_not_product_loc loc env sigma c =
  raise_pretype_error (loc, env, sigma, NotProduct (nf_evar sigma c))

(*s Error in conversion from AST to rawterms *)

let error_var_not_found_loc loc s =
  raise_pretype_error (loc, empty_env, Evd.empty, VarNotFound s)

