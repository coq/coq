(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Constr
open Vars
open Environ
open CClosure
open Context.Rel.Declaration

(****************************************************************************)
(*                   Reduction Functions                                    *)
(****************************************************************************)

let whd_all env t =
  match kind t with
    | (Sort _|Meta _|Evar _|Ind _|Construct _|
       Prod _|Lambda _|Fix _|CoFix _|Int _|Float _|Array _) -> t
    | App (c, _) ->
      begin match kind c with
      | Ind _ | Construct _ | Evar _ | Meta _ | Int _ | Float _ | Array _ -> t
      | Sort _ | Rel _ | Var _ | Cast _ | Prod _ | Lambda _ | LetIn _ | App _
        | Const _ |Case _ | Fix _ | CoFix _ | Proj _ ->
         whd_val (create_clos_infos RedFlags.all env) (create_tab ()) (inject t)
      end
    | Rel _ | Cast _ | LetIn _ | Case _ | Proj _ | Const _ | Var _ ->
        whd_val (create_clos_infos RedFlags.all env) (create_tab ()) (inject t)

let whd_allnolet env t =
  match kind t with
    | (Sort _|Meta _|Evar _|Ind _|Construct _|
       Prod _|Lambda _|Fix _|CoFix _|LetIn _|Int _|Float _|Array _) -> t
    | App (c, _) ->
      begin match kind c with
      | Ind _ | Construct _ | Evar _ | Meta _ | LetIn _ | Int _ | Float _ | Array _ -> t
      | Sort _ | Rel _ | Var _ | Cast _ | Prod _ | Lambda _ | App _
        | Const _ | Case _ | Fix _ | CoFix _ | Proj _ ->
         whd_val (create_clos_infos RedFlags.allnolet env) (create_tab ()) (inject t)
      end
    | Rel _ | Cast _ | Case _ | Proj _ | Const _ | Var _ ->
        whd_val (create_clos_infos RedFlags.allnolet env) (create_tab ()) (inject t)

(* Application with on-the-fly reduction *)

let beta_applist c l =
  let rec app subst c l =
    match kind c, l with
    | Lambda(_,_,c), arg::l -> app (arg::subst) c l
    | _ -> Term.applist (substl subst c, l) in
  app [] c l

let beta_appvect c v = beta_applist c (Array.to_list v)

let beta_app c a = beta_applist c [a]

(* Compatibility *)
let betazeta_appvect = Term.lambda_appvect_decls

(********************************************************************)
(*             Special-Purpose Reduction                            *)
(********************************************************************)

(* pseudo-reduction rule:
 * [hnf_prod_app env (Prod(_,B)) N --> B[N]
 * with an HNF on the first argument to produce a product.
 * if this does not work, then we use the string S as part of our
 * error message. *)

let hnf_prod_app env t n =
  match kind (whd_all env t) with
    | Prod (_,_,b) -> subst1 n b
    | _ -> anomaly ~label:"hnf_prod_app" (Pp.str "Need a product.")

let hnf_prod_applist env t nl =
  List.fold_left (hnf_prod_app env) t nl

let hnf_prod_applist_decls env n c l =
  let rec app n subst t l =
    if Int.equal n 0 then
      if l == [] then substl subst t
      else anomaly (Pp.str "Too many arguments.")
    else match kind (whd_allnolet env t), l with
    | Prod(_,_,c), arg::l -> app (n-1) (arg::subst) c l
    | LetIn(_,b,_,c), _ -> app (n-1) (substl subst b::subst) c l
    | _, [] -> anomaly (Pp.str "Not enough arguments.")
    | _ -> anomaly (Pp.str "Not enough prod/let's.") in
  app n [] c l

(* Dealing with arities *)

let hnf_decompose_prod env =
  let rec decrec env m c =
    let t = whd_all env c in
    match kind t with
      | Prod (n,a,c0) ->
          let d = LocalAssum (n,a) in
          decrec (push_rel d env) (Context.Rel.add d m) c0
      | _ -> m,t
  in
  decrec env Context.Rel.empty

let hnf_decompose_lambda env =
  let rec decrec env m c =
    let t = whd_all env c in
    match kind t with
      | Lambda (n,a,c0) ->
          let d = LocalAssum (n,a) in
          decrec (push_rel d env) (Context.Rel.add d m) c0
      | _ -> m,t
  in
  decrec env Context.Rel.empty

(* The same but preserving lets in the context, not internal ones. *)
let hnf_decompose_prod_decls env =
  let rec prodec_rec env l ty =
    let rty = whd_allnolet env ty in
    match kind rty with
    | Prod (x,t,c)  ->
        let d = LocalAssum (x,t) in
        prodec_rec (push_rel d env) (Context.Rel.add d l) c
    | LetIn (x,b,t,c) ->
        let d = LocalDef (x,b,t) in
        prodec_rec (push_rel d env) (Context.Rel.add d l) c
    | _               ->
      let rty' = whd_all env rty in
        if Constr.equal rty' rty then l, rty
        else prodec_rec env l rty'
  in
  prodec_rec env Context.Rel.empty

let hnf_decompose_lambda_decls env =
  let rec lamec_rec env l ty =
    let rty = whd_allnolet env ty in
    match kind rty with
    | Lambda (x,t,c)  ->
        let d = LocalAssum (x,t) in
        lamec_rec (push_rel d env) (Context.Rel.add d l) c
    | LetIn (x,b,t,c) ->
        let d = LocalDef (x,b,t) in
        lamec_rec (push_rel d env) (Context.Rel.add d l) c
    | _               -> l,rty
  in
  lamec_rec env Context.Rel.empty

let hnf_decompose_lambda_n_decls env n =
  let rec lamec_rec env n l c =
    if Int.equal n 0 then l,c
    else
    let rc = whd_allnolet env c in
    match kind rc with
    | Lambda (x,t,c)  ->
        let d = LocalAssum (x,t) in
        lamec_rec (push_rel d env) (n-1) (Context.Rel.add d l) c
    | LetIn (x,b,t,c) ->
        let d = LocalDef (x,b,t) in
        lamec_rec (push_rel d env) n (Context.Rel.add d l) c
    | _ -> anomaly (Pp.str "dest_lam_n_assum: not enough abstractions")
  in
  lamec_rec env n Context.Rel.empty

exception NotArity

let dest_arity env c =
  let l, c = hnf_decompose_prod_decls env c in
  match kind c with
    | Sort s -> l,s
    | _ -> raise NotArity

let is_arity env c =
  try
    let _ = dest_arity env c in
    true
  with NotArity -> false

let eta_expand env t ty =
  let ctxt, _codom = hnf_decompose_prod env ty in
  let ctxt',t = hnf_decompose_lambda env t in
  let d = Context.Rel.nhyps ctxt - Context.Rel.nhyps ctxt' in
  let eta_args = List.rev_map mkRel (List.interval 1 d) in
  let t = Term.applistc (Vars.lift d t) eta_args in
  let t = Term.it_mkLambda_or_LetIn t (List.firstn d ctxt) in
  Term.it_mkLambda_or_LetIn t ctxt'

(* Deprecated *)

let dest_prod       = hnf_decompose_prod
let dest_prod_assum = hnf_decompose_prod_decls
let dest_lam        = hnf_decompose_lambda
let dest_lam_assum  = hnf_decompose_lambda_decls
