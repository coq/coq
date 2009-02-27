(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util
open Stdpp
open Names
open Sign
open Term
open Termops
open Environ
open Type_errors
open Rawterm
open Inductiveops

type pretype_error =
  (* Old Case *)
  | CantFindCaseType of constr
  (* Unification *)
  | OccurCheck of existential_key * constr
  | NotClean of existential_key * constr * Evd.hole_kind
  | UnsolvableImplicit of Evd.evar_info * Evd.hole_kind * 
      Evd.unsolvability_explanation option
  | CannotUnify of constr * constr
  | CannotUnifyLocal of constr * constr * constr
  | CannotUnifyBindingType of constr * constr
  | CannotGeneralize of constr
  | NoOccurrenceFound of constr * identifier option
  | CannotFindWellTypedAbstraction of constr * constr list
  (* Pretyping *)
  | VarNotFound of identifier
  | UnexpectedType of constr * constr
  | NotProduct of constr

exception PretypeError of env * pretype_error

let precatchable_exception = function
  | Util.UserError _ | TypeError _ | PretypeError _
  | Stdpp.Exc_located(_,(Util.UserError _ | TypeError _ |
    Nametab.GlobalizationError _ | PretypeError _)) -> true
  | _ -> false

let nf_evar = Evd.nf_evar
let j_nf_evar sigma j = 
  { uj_val = nf_evar sigma j.uj_val;
    uj_type = nf_evar sigma j.uj_type }
let jl_nf_evar sigma jl = List.map (j_nf_evar sigma) jl
let jv_nf_evar sigma = Array.map (j_nf_evar sigma)
let tj_nf_evar sigma {utj_val=v;utj_type=t} =
  {utj_val=nf_evar sigma v;utj_type=t}

let env_ise sigma env =
  let sign = named_context_val env in
  let ctxt = rel_context env in
  let env0 = reset_with_named_context sign env in
  Sign.fold_rel_context
    (fun (na,b,ty) e ->
      push_rel
        (na, Option.map (nf_evar sigma) b, nf_evar sigma ty)
        e)
    ctxt
    ~init:env0

(* This simplify the typing context of Cases clauses *)
(* hope it does not disturb other typing contexts *)
let contract env lc =
  let l = ref [] in
  let contract_context (na,c,t) env =
    match c with
      | Some c' when isRel c' ->
	  l := (substl !l c') :: !l;
	  env
      | _ -> 
	  let t' = substl !l t in
	  let c' = Option.map (substl !l) c in
	  let na' = named_hd env t' na in
	  l := (mkRel 1) :: List.map (lift 1) !l;
	  push_rel (na',c',t') env in
  let env = process_rel_context contract_context env in
  (env, List.map (substl !l) lc)

let contract2 env a b = match contract env [a;b] with
  | env, [a;b] -> env,a,b | _ -> assert false

let contract3 env a b c = match contract env [a;b;c] with
  | env, [a;b;c] -> env,a,b,c | _ -> assert false

let raise_pretype_error (loc,ctx,sigma,te) =
  Stdpp.raise_with_loc loc (PretypeError(env_ise sigma ctx,te))

let raise_located_type_error (loc,ctx,sigma,te) =
  Stdpp.raise_with_loc loc (TypeError(env_ise sigma ctx,te))


let error_actual_type_loc loc env sigma {uj_val=c;uj_type=actty} expty =
  let env, c, actty, expty = contract3 env c actty expty in
  let j = j_nf_evar sigma {uj_val=c;uj_type=actty} in
  raise_located_type_error
    (loc, env, sigma, ActualType (j, nf_evar sigma expty))

let error_cant_apply_not_functional_loc loc env sigma rator randl =
  let ja = Array.of_list (jl_nf_evar sigma randl) in
  raise_located_type_error
    (loc, env, sigma,
    CantApplyNonFunctional (j_nf_evar sigma rator, ja))

let error_cant_apply_bad_type_loc loc env sigma (n,c,t) rator randl =
  let ja = Array.of_list (jl_nf_evar sigma randl) in
  raise_located_type_error
    (loc, env, sigma,
     CantApplyBadType
       ((n,nf_evar sigma c, nf_evar sigma t),
        j_nf_evar sigma rator, ja))

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

let error_not_a_type_loc loc env sigma j =
  raise_located_type_error (loc, env, sigma, NotAType (j_nf_evar sigma j))

(*s Implicit arguments synthesis errors. It is hard to find
    a precise location. *)

let error_occur_check env sigma ev c =
  let c = nf_evar sigma c in
  raise (PretypeError (env_ise sigma env, OccurCheck (ev,c)))

let error_not_clean env sigma ev c (loc,k) =
  let c = nf_evar sigma c in
  raise_with_loc loc
    (PretypeError (env_ise sigma env,  NotClean (ev,c,k)))

let error_unsolvable_implicit loc env sigma evi e explain =
  raise_with_loc loc
    (PretypeError (env_ise sigma env, UnsolvableImplicit (evi, e, explain)))

let error_cannot_unify env sigma (m,n) =
  raise (PretypeError (env_ise sigma env,CannotUnify (m,n)))

let error_cannot_unify_local env sigma (m,n,sn) = 
  raise (PretypeError (env_ise sigma env,CannotUnifyLocal (m,n,sn)))

let error_cannot_coerce env sigma (m,n) =
  raise (PretypeError (env_ise sigma env,CannotUnify (m,n)))

let error_cannot_find_well_typed_abstraction env sigma p l =
  raise (PretypeError (env_ise sigma env,CannotFindWellTypedAbstraction (p,l)))

(*s Ml Case errors *)

let error_cant_find_case_type_loc loc env sigma expr =
  raise_pretype_error
    (loc, env, sigma, CantFindCaseType (nf_evar sigma expr))

(*s Pretyping errors *)

let error_unexpected_type_loc loc env sigma actty expty =
  let env, actty, expty = contract2 env actty expty in
  raise_pretype_error
    (loc, env, sigma,
     UnexpectedType (nf_evar sigma actty, nf_evar sigma expty))

let error_not_product_loc loc env sigma c =
  raise_pretype_error (loc, env, sigma, NotProduct (nf_evar sigma c))

(*s Error in conversion from AST to rawterms *)

let error_var_not_found_loc loc s =
  raise_pretype_error (loc, empty_env, Evd.empty, VarNotFound s)
