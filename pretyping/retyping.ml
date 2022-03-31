(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open Term
open Constr
open Context
open Inductive
open Inductiveops
open Names
open Reductionops
open Environ
open Termops
open EConstr
open Vars
open Arguments_renaming
open Context.Rel.Declaration

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

type retype_error =
  | NotASort
  | NotAnArity
  | NotAType
  | BadRel
  | BadVariable of Id.t
  | BadMeta of int
  | BadRecursiveType
  | NonFunctionalConstruction

let print_retype_error = function
  | NotASort -> str "Not a sort"
  | NotAnArity -> str "Not an arity"
  | NotAType -> str "Not a type (1)"
  | BadRel -> str "unbound local variable"
  | BadVariable id -> str "variable " ++ Id.print id ++ str " unbound"
  | BadMeta n -> str "unknown meta " ++ int n
  | BadRecursiveType -> str "Bad recursive type"
  | NonFunctionalConstruction -> str "Non-functional construction"

exception RetypeError of retype_error

let retype_error re = raise (RetypeError re)

let anomaly_on_error f x =
 try f x
 with RetypeError e -> anomaly ~label:"retyping" (print_retype_error e ++ str ".")

let get_type_from_constraints env sigma t =
  if isEvar sigma (fst (decompose_app_vect sigma t)) then
    match
      List.map_filter (fun (pbty,env,t1,t2) ->
        if is_fconv Reduction.CONV env sigma t t1 then Some t2
        else if is_fconv Reduction.CONV env sigma t t2 then Some t1
        else None)
        (snd (Evd.extract_all_conv_pbs sigma))
    with
    | t::l -> t
    | _ -> raise Not_found
  else raise Not_found

let sort_of_arity_with_constraints env sigma t =
  try Reductionops.sort_of_arity env sigma t
  with Reduction.NotArity ->
  try
    let t = get_type_from_constraints env sigma t in
    Reductionops.sort_of_arity env sigma t
  with Not_found | Reduction.NotArity -> retype_error NotAnArity

let rec subst_type env sigma subs typ = function
  | [] -> substl subs typ
  | h::rest ->
    (* Fast path if the type is already a product *)
    match EConstr.kind sigma typ with
    | Prod (_, _, c2) -> subst_type env sigma (h :: subs) c2 rest
    | _ ->
      let typ = substl subs typ in
      match EConstr.kind sigma (whd_all env sigma typ) with
        | Prod (_, _, c2) -> subst_type env sigma [h] c2 rest
        | _ -> retype_error NonFunctionalConstruction

let subst_type env sigma typ args = subst_type env sigma [] typ args

(* If ft is the type of f which itself is applied to args, *)
(* [sort_of_atomic_type] computes ft[args] which has to be a sort *)

let sort_of_atomic_type env sigma ft args =
  let rec concl_of_arity env n ar args =
    match EConstr.kind sigma (whd_all env sigma ar), args with
    | Prod (na, t, b), h::l ->
      concl_of_arity (push_rel (LocalDef (na, lift n h, t)) env) (n + 1) b l
    | Sort s, [] -> ESorts.kind sigma s
    | _ -> retype_error NotASort
  in concl_of_arity env 0 ft (Array.to_list args)

let type_of_var env id =
  try NamedDecl.get_type (lookup_named id env)
  with Not_found -> retype_error (BadVariable id)

let decomp_sort env sigma t =
  match EConstr.kind sigma (whd_all env sigma t) with
  | Sort s -> ESorts.kind sigma s
  | _ -> retype_error NotASort

let destSort sigma s = ESorts.kind sigma (destSort sigma s)

let betazetaevar_applist sigma n c l =
  let rec stacklam n env t stack =
    if Int.equal n 0 then applist (substl env t, stack) else
    match EConstr.kind sigma t, stack with
    | Lambda(_,_,c), arg::stacktl -> stacklam (n-1) (arg::env) c stacktl
    | LetIn(_,b,_,c), _ -> stacklam (n-1) (substl env b::env) c stack
    | Evar _, _ -> applist (substl env t, stack)
    | _ -> anomaly (Pp.str "Not enough lambda/let's.") in
  stacklam n [] c l

let retype ?(polyprop=true) sigma =
  let rec type_of env cstr =
    match EConstr.kind sigma cstr with
    | Meta n ->
      (try strip_outer_cast sigma (Evd.meta_ftype sigma n).Evd.rebus
       with Not_found -> retype_error (BadMeta n))
    | Rel n ->
      let ty = try RelDecl.get_type (lookup_rel n env)
        with Not_found -> retype_error BadRel
      in
      lift n ty
    | Var id -> type_of_var env id
    | Const (cst, u) -> EConstr.of_constr (rename_type_of_constant env (cst, EInstance.kind sigma u))
    | Evar ev -> existential_type sigma ev
    | Ind (ind, u) -> EConstr.of_constr (rename_type_of_inductive env (ind, EInstance.kind sigma u))
    | Construct (cstr, u) -> EConstr.of_constr (rename_type_of_constructor env (cstr, EInstance.kind sigma u))
    | Case (ci,u,pms,p,iv,c,lf) ->
        let (_,p,iv,c,lf) = EConstr.expand_case env sigma (ci,u,pms,p,iv,c,lf) in
        let Inductiveops.IndType(indf,realargs) =
          let t = type_of env c in
          try Inductiveops.find_rectype env sigma t
          with Not_found ->
          try
            let t = get_type_from_constraints env sigma t in
            Inductiveops.find_rectype env sigma t
          with Not_found -> retype_error BadRecursiveType
        in
        let n = inductive_nrealdecls env (fst (fst (dest_ind_family indf))) in
        let t = betazetaevar_applist sigma n p realargs in
        (match EConstr.kind sigma (whd_all env sigma (type_of env t)) with
          | Prod _ -> whd_beta env sigma (applist (t, [c]))
          | _ -> t)
    | Lambda (name,c1,c2) ->
          mkProd (name, c1, type_of (push_rel (LocalAssum (name,c1)) env) c2)
    | LetIn (name,b,c1,c2) ->
         subst1 b (type_of (push_rel (LocalDef (name,b,c1)) env) c2)
    | Fix ((_,i),(_,tys,_)) -> tys.(i)
    | CoFix (i,(_,tys,_)) -> tys.(i)
    | App(f,args) when Termops.is_template_polymorphic_ind env sigma f ->
        let t = type_of_global_reference_knowing_parameters env f args in
        strip_outer_cast sigma (subst_type env sigma t (Array.to_list args))
    | App(f,args) ->
        strip_outer_cast sigma
          (subst_type env sigma (type_of env f) (Array.to_list args))
    | Proj (p,c) ->
       let ty = type_of env c in
       EConstr.of_constr (try
           Inductiveops.type_of_projection_knowing_arg env sigma p c ty
         with Invalid_argument _ -> retype_error BadRecursiveType)
    | Cast (c,_, t) -> t
    | Sort _ | Prod _ -> mkSort (sort_of env cstr)
    | Int _ -> EConstr.of_constr (Typeops.type_of_int env)
    | Float _ -> EConstr.of_constr (Typeops.type_of_float env)
    | Array(u, _, _, ty) ->
      let arr = EConstr.of_constr @@ Typeops.type_of_array env (EInstance.kind sigma u) in
      mkApp(arr, [|ty|])

  and sort_of env t =
    match EConstr.kind sigma t with
    | Cast (c,_, s) when isSort sigma s -> destSort sigma s
    | Sort s ->
      begin match ESorts.kind sigma s with
      | SProp | Prop | Set -> Sorts.type1
      | Type u -> Sorts.sort_of_univ (Univ.Universe.super u)
      end
    | Prod (name,t,c2) ->
      let dom = sort_of env t in
      let rang = sort_of (push_rel (LocalAssum (name,t)) env) c2 in
      Typeops.sort_of_product env dom rang
    | App(f,args) when Termops.is_template_polymorphic_ind env sigma f ->
      let t = type_of_global_reference_knowing_parameters env f args in
        sort_of_atomic_type env sigma t args
    | App(f,args) -> sort_of_atomic_type env sigma (type_of env f) args
    | Lambda _ | Fix _ | Construct _ -> retype_error NotAType
    | _ -> decomp_sort env sigma (type_of env t)

  and type_of_global_reference_knowing_parameters env c args =
    match EConstr.kind sigma c with
    | Ind (ind, u) ->
      let u = EInstance.kind sigma u in
      let mip = lookup_mind_specif env ind in
      let paramtyps = Array.map_to_list (fun arg () ->
          let t = type_of env arg in
          let s = sort_of_arity_with_constraints env sigma t in
          ESorts.kind sigma s)
          args
      in
      EConstr.of_constr
        (Inductive.type_of_inductive_knowing_parameters
           ~polyprop (mip, u) paramtyps)
    | Construct (cstr, u) ->
      let u = EInstance.kind sigma u in
      EConstr.of_constr (type_of_constructor env (cstr, u))
    | _ -> assert false

  in type_of, sort_of, type_of_global_reference_knowing_parameters

let get_sort_family_of ?(polyprop=true) env sigma t =
  let type_of,_,type_of_global_reference_knowing_parameters = retype ~polyprop sigma in
  let rec sort_family_of env t =
    match EConstr.kind sigma t with
    | Cast (c,_, s) when isSort sigma s -> Sorts.family (destSort sigma s)
    | Sort _ -> InType
    | Prod (name,t,c2) ->
        let s2 = sort_family_of (push_rel (LocalAssum (name,t)) env) c2 in
        if not (is_impredicative_set env) &&
           s2 == InSet && sort_family_of env t == InType then InType else s2
    | App(f,args) when Termops.is_template_polymorphic_ind env sigma f ->
        let t = type_of_global_reference_knowing_parameters env f args in
        Sorts.family (sort_of_atomic_type env sigma t args)
    | App(f,args) ->
        Sorts.family (sort_of_atomic_type env sigma (type_of env f) args)
    | Lambda _ | Fix _ | Construct _ -> retype_error NotAType
    | _ ->
      Sorts.family (decomp_sort env sigma (type_of env t))
  in sort_family_of env t

let get_sort_of ?(polyprop=true) env sigma t =
  let _,f,_ = retype ~polyprop sigma in anomaly_on_error (f env) t
let type_of_global_reference_knowing_parameters env sigma c args =
  let _,_,f = retype sigma in anomaly_on_error (f env c) args

let type_of_global_reference_knowing_conclusion env sigma c conclty =
  match EConstr.kind sigma c with
    | Ind (ind,u) ->
        let spec = Inductive.lookup_mind_specif env ind in
          type_of_inductive_knowing_conclusion env sigma (spec, EInstance.kind sigma u) conclty
    | Const (cst, u) ->
        let t = constant_type_in env (cst, EInstance.kind sigma u) in
          sigma, EConstr.of_constr t
    | Var id -> sigma, type_of_var env id
    | Construct (cstr, u) -> sigma, EConstr.of_constr (type_of_constructor env (cstr, EInstance.kind sigma u))
    | _ -> assert false

let get_type_of ?(polyprop=true) ?(lax=false) env sigma c =
  let f,_,_ = retype ~polyprop sigma in
    if lax then f env c else anomaly_on_error (f env) c

(* Makes an unsafe judgment from a constr *)
let get_judgment_of env evc c = { uj_val = c; uj_type = get_type_of env evc c }

let get_type_of_constr ?polyprop ?lax env ?(uctx=UState.from_env env) c =
  EConstr.Unsafe.to_constr (get_type_of ?polyprop ?lax env (Evd.from_ctx uctx) (EConstr.of_constr c))

(* Returns sorts of a context *)
let sorts_of_context env evc ctxt =
  let rec aux = function
  | [] -> env,[]
  | d :: ctxt ->
      let env,sorts = aux ctxt in
      let s = get_sort_of env evc (RelDecl.get_type d) in
      (push_rel d env,s::sorts) in
  snd (aux ctxt)

let expand_projection env sigma pr c args =
  let ty = get_type_of ~lax:true env sigma c in
  let (i,u), ind_args =
    try Inductiveops.find_mrectype env sigma ty
    with Not_found -> retype_error BadRecursiveType
  in
    mkApp (mkConstU (Projection.constant pr,u),
           Array.of_list (ind_args @ (c :: args)))

let relevance_of_term env sigma c =
  if Environ.sprop_allowed env then
    let rec aux rels c =
      match kind sigma c with
      | Rel n ->
        let len = Range.length rels in
        if n <= len then Range.get rels (n - 1)
        else Relevanceops.relevance_of_rel env (n - len)
      | Var x -> Relevanceops.relevance_of_var env x
      | Sort _ -> Sorts.Relevant
      | Cast (c, _, _) -> aux rels c
      | Prod _ -> Sorts.Relevant
      | Lambda ({binder_relevance=r}, _, bdy) ->
        aux (Range.cons r rels) bdy
      | LetIn ({binder_relevance=r}, _, _, bdy) ->
        aux (Range.cons r rels) bdy
      | App (c, _) -> aux rels c
      | Const (c,_) -> Relevanceops.relevance_of_constant env c
      | Ind _ -> Sorts.Relevant
      | Construct (c,_) -> Relevanceops.relevance_of_constructor env c
      | Case (ci, _, _, _, _, _, _) -> ci.ci_relevance
      | Fix ((_,i),(lna,_,_)) -> (lna.(i)).binder_relevance
      | CoFix (i,(lna,_,_)) -> (lna.(i)).binder_relevance
      | Proj (p, _) -> Relevanceops.relevance_of_projection env p
      | Int _ | Float _ | Array _ -> Sorts.Relevant
      | Meta _ | Evar _ -> Sorts.Relevant

    in
    aux Range.empty c
  else Sorts.Relevant

let relevance_of_type env sigma t =
  let s = get_sort_family_of env sigma t in
  Sorts.relevance_of_sort_family s

let relevance_of_sort s = Sorts.relevance_of_sort (EConstr.Unsafe.to_sorts s)

let relevance_of_sort_family f =  Sorts.relevance_of_sort_family f
