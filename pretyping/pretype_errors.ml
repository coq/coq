(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Term
open Environ
open Type_errors

type unification_error =
  | OccurCheck of existential_key * constr
  | NotClean of existential * env * constr
  | NotSameArgSize
  | NotSameHead
  | NoCanonicalStructure
  | ConversionFailed of env * constr * constr
  | MetaOccurInBody of existential_key
  | InstanceNotSameType of existential_key * env * types * types
  | UnifUnivInconsistency of Univ.univ_inconsistency
  | CannotSolveConstraint of Evd.evar_constraint * unification_error

type position = (Id.t * Locus.hyp_location_flag) option

type position_reporting = (position * int) * constr

type subterm_unification_error = bool * position_reporting * position_reporting * (constr * constr * unification_error) option

type pretype_error =
  (* Old Case *)
  | CantFindCaseType of constr
  (* Type inference unification *)
  | ActualTypeNotCoercible of unsafe_judgment * types * unification_error
  (* Tactic unification *)
  | UnifOccurCheck of existential_key * constr
  | UnsolvableImplicit of existential_key * Evd.unsolvability_explanation option
  | CannotUnify of constr * constr * unification_error option
  | CannotUnifyLocal of constr * constr * constr
  | CannotUnifyBindingType of constr * constr
  | CannotGeneralize of constr
  | NoOccurrenceFound of constr * Id.t option
  | CannotFindWellTypedAbstraction of constr * constr list * (env * type_error) option
  | WrongAbstractionType of Name.t * constr * types * types
  | AbstractionOverMeta of Name.t * Name.t
  | NonLinearUnification of Name.t * constr
  (* Pretyping *)
  | VarNotFound of Id.t
  | UnexpectedType of constr * constr
  | NotProduct of constr
  | TypingError of type_error
  | CannotUnifyOccurrences of subterm_unification_error
  | UnsatisfiableConstraints of
    (existential_key * Evar_kinds.t) option * Evar.Set.t option

exception PretypeError of env * Evd.evar_map * pretype_error

let precatchable_exception = function
  | Errors.UserError _ | TypeError _ | PretypeError _
  | Nametab.GlobalizationError _ -> true
  | _ -> false

let raise_pretype_error (loc,env,sigma,te) =
  Loc.raise loc (PretypeError(env,sigma,te))

let raise_located_type_error (loc,env,sigma,te) =
  Loc.raise loc (PretypeError(env,sigma,TypingError te))


let error_actual_type_loc loc env sigma {uj_val=c;uj_type=actty} expty reason =
  let j = {uj_val=c;uj_type=actty} in
  raise_pretype_error
    (loc, env, sigma, ActualTypeNotCoercible (j, expty, reason))

let error_cant_apply_not_functional_loc loc env sigma rator randl =
  raise_located_type_error
    (loc, env, sigma, CantApplyNonFunctional (rator, Array.of_list randl))

let error_cant_apply_bad_type_loc loc env sigma (n,c,t) rator randl =
  raise_located_type_error
    (loc, env, sigma,
       CantApplyBadType ((n,c,t), rator, Array.of_list randl))

let error_ill_formed_branch_loc loc env sigma c i actty expty =
  raise_located_type_error
    (loc, env, sigma, IllFormedBranch (c, i, actty, expty))

let error_number_branches_loc loc env sigma cj expn =
  raise_located_type_error (loc, env, sigma, NumberBranches (cj, expn))

let error_case_not_inductive_loc loc env sigma cj =
  raise_located_type_error (loc, env, sigma, CaseNotInductive cj)

let error_ill_typed_rec_body_loc loc env sigma i na jl tys =
  raise_located_type_error
    (loc, env, sigma, IllTypedRecBody (i, na, jl, tys))

let error_not_a_type_loc loc env sigma j =
  raise_located_type_error (loc, env, sigma, NotAType j)

(*s Implicit arguments synthesis errors. It is hard to find
    a precise location. *)

let error_occur_check env sigma ev c =
  raise (PretypeError (env, sigma, UnifOccurCheck (ev,c)))

let error_unsolvable_implicit loc env sigma evk explain =
  Loc.raise loc
    (PretypeError (env, sigma, UnsolvableImplicit (evk, explain)))

let error_cannot_unify_loc loc env sigma ?reason (m,n) =
  Loc.raise loc (PretypeError (env, sigma,CannotUnify (m,n,reason)))

let error_cannot_unify env sigma ?reason (m,n) =
  raise (PretypeError (env, sigma,CannotUnify (m,n,reason)))

let error_cannot_unify_local env sigma (m,n,sn) =
  raise (PretypeError (env, sigma,CannotUnifyLocal (m,n,sn)))

let error_cannot_coerce env sigma (m,n) =
  raise (PretypeError (env, sigma,CannotUnify (m,n,None)))

let error_cannot_find_well_typed_abstraction env sigma p l e =
  raise (PretypeError (env, sigma,CannotFindWellTypedAbstraction (p,l,e)))

let error_wrong_abstraction_type env sigma na a p l =
  raise (PretypeError (env, sigma,WrongAbstractionType (na,a,p,l)))

let error_abstraction_over_meta env sigma hdmeta metaarg =
  let m = Evd.meta_name sigma hdmeta and n = Evd.meta_name sigma metaarg in
  raise (PretypeError (env, sigma,AbstractionOverMeta (m,n)))

let error_non_linear_unification env sigma hdmeta t =
  let m = Evd.meta_name sigma hdmeta in
  raise (PretypeError (env, sigma,NonLinearUnification (m,t)))

(*s Ml Case errors *)

let error_cant_find_case_type_loc loc env sigma expr =
  raise_pretype_error (loc, env, sigma, CantFindCaseType expr)

(*s Pretyping errors *)

let error_unexpected_type_loc loc env sigma actty expty =
  raise_pretype_error (loc, env, sigma, UnexpectedType (actty, expty))

let error_not_product_loc loc env sigma c =
  raise_pretype_error (loc, env, sigma, NotProduct c)

(*s Error in conversion from AST to glob_constr *)

let error_var_not_found_loc loc s =
  raise_pretype_error (loc, empty_env, Evd.empty, VarNotFound s)

(*s Typeclass errors *)

let unsatisfiable_constraints env evd ev comp =
  match ev with
  | None ->
    let err = UnsatisfiableConstraints (None, comp) in
    raise (PretypeError (env,evd,err))
  | Some ev ->
    let loc, kind = Evd.evar_source ev evd in
    let err = UnsatisfiableConstraints (Some (ev, kind), comp) in
    Loc.raise loc (PretypeError (env,evd,err))

let unsatisfiable_exception exn =
  match exn with
  | PretypeError (_, _, UnsatisfiableConstraints _) -> true
  | _ -> false
