(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module CVars = Vars

open Pp
open CErrors
open Util
open Term
open Constr
open Context
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
  | BadEvar of Evar.t
  | BadMeta of int
  | BadRecursiveType
  | NonFunctionalConstruction

let print_retype_error = function
  | NotASort -> str "Not a sort"
  | NotAnArity -> str "Not an arity"
  | NotAType -> str "Not a type"
  | BadRel -> str "Unbound local variable"
  | BadVariable id -> str "Variable " ++ Id.print id ++ str " unbound"
  | BadEvar e -> str "Unknown evar " ++ Evar.print e
  | BadMeta n -> str "Unknown meta " ++ int n
  | BadRecursiveType -> str "Bad recursive type"
  | NonFunctionalConstruction -> str "Non-functional construction"

exception RetypeError of retype_error

let retype_error re = raise (RetypeError re)

let anomaly_on_error f x =
 try f x
 with RetypeError e -> anomaly ~label:"retyping" (print_retype_error e ++ str ".")

let get_type_from_constraints env sigma t =
  if isEvar sigma (fst (decompose_app sigma t)) then
    match
      List.map_filter (fun (pbty,env,t1,t2) ->
        if is_fconv Conversion.CONV env sigma t t1 then Some t2
        else if is_fconv Conversion.CONV env sigma t t2 then Some t1
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
    | Sort s, [] -> s
    | _ -> retype_error NotASort
  in concl_of_arity env 0 ft (Array.to_list args)

let type_of_var env id =
  try NamedDecl.get_type (lookup_named id env)
  with Not_found -> retype_error (BadVariable id)

let decomp_sort env sigma t =
  let t = whd_all env sigma t in
  match EConstr.kind sigma t with
  | Sort s -> s
  | _ ->
    let t = try get_type_from_constraints env sigma t
      with Not_found -> retype_error NotASort
    in
    match EConstr.kind sigma (whd_all env sigma t) with
    | Sort s -> s
    | _ -> retype_error NotASort

let betazetaevar_applist sigma n c l =
  let rec stacklam n env t stack =
    if Int.equal n 0 then applist (substl env t, stack) else
    match EConstr.kind sigma t, stack with
    | Lambda(_,_,c), arg::stacktl -> stacklam (n-1) (arg::env) c stacktl
    | LetIn(_,b,_,c), _ -> stacklam (n-1) (substl env b::env) c stack
    | Evar _, _ -> applist (substl env t, stack)
    | _ -> anomaly (Pp.str "Not enough lambda/let's.") in
  stacklam n [] c l

let type_of_constant env sigma (c,u) =
  let cb = lookup_constant c env in
  let () = check_hyps_inclusion env sigma (GlobRef.ConstRef c) cb.const_hyps in
  let ty = CVars.subst_instance_constr (EConstr.Unsafe.to_instance u) cb.const_type in
  EConstr.of_constr (rename_type ty (GlobRef.ConstRef c))

let safe_meta_type metas n = match metas with
| None -> None
| Some f -> f n

exception SingletonInductiveBecomesProp of inductive

let template_sort ~forbid_polyprop subst (s:Sorts.t) =
  let s' = Inductive.Template.template_subst_sort subst s in
  let () = match forbid_polyprop with
    | None -> ()
    | Some indna ->
      if Sorts.is_prop s' && not (Sorts.is_prop s) then
        raise (SingletonInductiveBecomesProp indna)
  in
  ESorts.make s'

let bind_template bind_sort s (qsubst,usubst) =
  let qbind, ubind = Inductive.Template.bind_kind bind_sort in
  let qsubst = match qbind with
    | None -> qsubst
    | Some qbind ->
      let sq = Sorts.quality s in
      Int.Map.update qbind (function
          | None -> Some sq
          | Some q0 -> Some (Inductive.Template.max_template_quality q0 sq))
        qsubst
  in
  let usubst = match ubind with
    | None -> usubst
    | Some ubind ->
      let u = match s with
        | SProp | Prop | Set -> Univ.Universe.type0
        | Type u | QSort (_,u) -> u
      in
      Int.Map.update ubind (function
          | None -> Some u
          | Some _ ->
            CErrors.anomaly Pp.(str "Retyping.bind_template found non linear template level."))
        usubst
  in
  qsubst, usubst

let rec finish_template ~forbid_polyprop usubst = let open TemplateArity in function
  | CtorType (_,typ) -> typ
  | IndType (_, ctx, s) ->
    let s = template_sort ~forbid_polyprop usubst s in
    mkArity (ctx,s)
  | DefParam (na,v,t,codom) ->
    let codom = finish_template ~forbid_polyprop usubst codom in
    mkLetIn (na,v,t,codom)
  | NonTemplateArg (na,dom,codom) ->
    let codom = finish_template ~forbid_polyprop usubst codom in
    mkProd (na,dom,codom)
  | TemplateArg (na,ctx,binder,codom) ->
    let usubst = bind_template binder.bind_sort binder.default usubst in
    let codom = finish_template ~forbid_polyprop usubst codom in
    mkProd (na, mkArity (ctx, ESorts.make binder.default), codom)

let rec type_of_template_knowing_parameters ~forbid_polyprop arity_sort_of usubst typ args =
  let open TemplateArity in
  match args, typ with
  | [], _
  | _, (CtorType _ | IndType _) ->
    finish_template ~forbid_polyprop usubst typ
  | _, DefParam (na, v, t, codom) ->
    let codom = type_of_template_knowing_parameters ~forbid_polyprop arity_sort_of usubst codom args in
    mkLetIn (na, v, t, codom)
  | _ :: args, NonTemplateArg (na, dom, codom) ->
    let codom = type_of_template_knowing_parameters ~forbid_polyprop arity_sort_of usubst codom args in
    mkProd (na, dom, codom)
  | arg :: args, TemplateArg (na, ctx, binder, codom) ->
    let s = arity_sort_of arg in
    let usubst = bind_template binder.bind_sort s usubst in
    let codom = type_of_template_knowing_parameters ~forbid_polyprop arity_sort_of usubst codom args in
    (* typing ensures [ctx -> s] is correct *)
    mkProd (na, mkArity (ctx, ESorts.make s), codom)

let type_of_template_knowing_parameters ~forbid_polyprop arity_sort_of typ args =
  let empty_subst = Int.Map.empty, Int.Map.empty in
  type_of_template_knowing_parameters ~forbid_polyprop arity_sort_of empty_subst typ args

let retype ?metas ?(polyprop=true) sigma =
  let rec type_of env cstr =
    match EConstr.kind sigma cstr with
    | Meta n ->
      begin match safe_meta_type metas n with
      | None -> retype_error (BadMeta n)
      | Some ty -> strip_outer_cast sigma ty
      end
    | Rel n ->
      let ty = try RelDecl.get_type (lookup_rel n env)
        with Not_found -> retype_error BadRel
      in
      lift n ty
    | Var id -> type_of_var env id
    | Const c -> type_of_constant env sigma c
    | Evar ev -> begin match Evd.existential_type_opt sigma ev with
        | Some t -> t
        | None -> retype_error (BadEvar (fst ev))
      end
    | Ind ind -> Inductiveops.e_type_of_inductive env sigma ind
    | Construct c -> Inductiveops.e_type_of_constructor env sigma c
    | Case (ci,u,pms,p,iv,c,lf) ->
        let (_,(p,_),iv,c,lf) = EConstr.expand_case env sigma (ci,u,pms,p,iv,c,lf) in
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
    | App(f,args) ->
      if Termops.is_template_polymorphic_ref env sigma f then
        substituted_type_of_global_reference_knowing_parameters env f args
      else
        strip_outer_cast sigma
          (subst_type env sigma (type_of env f) (Array.to_list args))
    | Proj (p,_,c) ->
      let ty = type_of env c in
      (try Inductiveops.type_of_projection_knowing_arg env sigma p c ty
        with Invalid_argument _ -> retype_error BadRecursiveType)
    | Cast (c,_, t) -> t
    | Sort _ | Prod _ -> mkSort (sort_of env cstr)
    | Int _ -> EConstr.of_constr (Typeops.type_of_int env)
    | Float _ -> EConstr.of_constr (Typeops.type_of_float env)
    | String _ -> EConstr.of_constr (Typeops.type_of_string env)
    | Array(u, _, _, ty) ->
      let arr = EConstr.of_constr @@ Typeops.type_of_array env (EInstance.kind sigma u) in
      mkApp(arr, [|ty|])

  and sort_of env t : ESorts.t =
    match EConstr.kind sigma t with
    | Cast (c,_, s) when isSort sigma s -> destSort sigma s
    | Sort s ->
      begin match ESorts.kind sigma s with
      | SProp | Prop | Set -> ESorts.type1
      | Type u | QSort (_, u) -> ESorts.make (Sorts.sort_of_univ (Univ.Universe.super u))
      end
    | Prod (name,t,c2) ->
      let dom = sort_of env t in
      let rang = sort_of (push_rel (LocalAssum (name,t)) env) c2 in
      ESorts.make (Typeops.sort_of_product env (ESorts.kind sigma dom) (ESorts.kind sigma rang))
    | App(f,args) when Termops.is_template_polymorphic_ind env sigma f ->
      let t = type_of_global_reference_knowing_parameters env f args in
      sort_of_atomic_type env sigma t args
    | App(f,args) -> sort_of_atomic_type env sigma (type_of env f) args
    | Lambda _ | Fix _ | Construct _ -> retype_error NotAType
    | _ -> decomp_sort env sigma (type_of env t)

  and substituted_type_of_global_reference_knowing_parameters env c args =
    match EConstr.kind sigma c with
    | Ind (ind, u) ->
      let ty = type_of_global_reference_knowing_parameters env c args in
      strip_outer_cast sigma (subst_type env sigma ty (Array.to_list args))
    | Construct ((ind, i as ctor), u) ->
      let mib, mip = Inductive.lookup_mind_specif env ind in
      let ty =
        if mib.mind_nparams <= Array.length args then
        (* Fully applied parameters, we do not have to substitute *)
          EConstr.of_constr (rename_type mip.mind_user_lc.(i - 1) (ConstructRef ctor))
      else
        type_of_global_reference_knowing_parameters env c args
      in
      strip_outer_cast sigma (subst_type env sigma ty (Array.to_list args))
    | _ -> assert false

  and type_of_global_reference_knowing_parameters env c args =
    let arity_sort_of arg =
      let t = type_of env arg in
      let s = sort_of_arity_with_constraints env sigma t in
      ESorts.kind sigma s
    in
    let rename_type typ gr =
      EConstr.of_constr @@ rename_type (EConstr.Unsafe.to_constr typ) gr
    in
    match EConstr.kind sigma c with
    | Ind (ind, _) ->
      let typ = TemplateArity.get_template_arity env ind ~ctoropt:None in
      let forbid_polyprop = if polyprop then None
        else Some ind
      in
      let typ = type_of_template_knowing_parameters ~forbid_polyprop arity_sort_of typ (Array.to_list args) in
      rename_type typ (IndRef ind)
    | Construct ((ind,ctor as cstr), _) ->
      let typ = TemplateArity.get_template_arity env ind ~ctoropt:(Some ctor) in
      let typ = type_of_template_knowing_parameters ~forbid_polyprop:None arity_sort_of typ (Array.to_list args) in
      rename_type typ (ConstructRef cstr)
    | _ -> assert false

  in type_of, sort_of, type_of_global_reference_knowing_parameters

let get_sort_family_of ?(polyprop=true) env sigma t =
  let type_of,_,type_of_global_reference_knowing_parameters = retype ~polyprop sigma in
  let rec sort_family_of env t =
    match EConstr.kind sigma t with
    | Cast (c,_, s) when isSort sigma s -> ESorts.family sigma (destSort sigma s)
    | Sort _ -> InType
    | Prod (name,t,c2) ->
        let s2 = sort_family_of (push_rel (LocalAssum (name,t)) env) c2 in
        if not (is_impredicative_set env) &&
           s2 == InSet && sort_family_of env t == InType then InType else s2
    | App(f,args) when Termops.is_template_polymorphic_ind env sigma f ->
        let t = type_of_global_reference_knowing_parameters env f args in
        ESorts.family sigma (sort_of_atomic_type env sigma t args)
    | App(f,args) ->
        ESorts.family sigma (sort_of_atomic_type env sigma (type_of env f) args)
    | Lambda _ | Fix _ | Construct _ -> retype_error NotAType
    | _ ->
      ESorts.family sigma (decomp_sort env sigma (type_of env t))
  in sort_family_of env t

let get_sort_of ?(polyprop=true) env sigma t =
  let _,f,_ = retype ~polyprop sigma in anomaly_on_error (f env) t
let type_of_global_reference_knowing_parameters env sigma c args =
  let _,_,f = retype sigma in anomaly_on_error (f env c) args

let get_type_of ?metas ?(polyprop=true) ?(lax=false) env sigma c =
  let f,_,_ = retype ?metas ~polyprop sigma in
    if lax then f env c else anomaly_on_error (f env) c

let rec check_named env sigma c =
  match EConstr.kind sigma c with
  | Var id ->
    (try ignore (lookup_named id env)
     with Not_found -> retype_error (BadVariable id))
  | Evar _ ->
    (* This is cheating, but some devs exploit that a
       dependency in the evar args may disappear *)
    ()
  | _ -> EConstr.iter sigma (check_named env sigma) c

let reinterpret_get_type_of ~src env sigma c =
  try
    check_named env sigma c;
    get_type_of ~lax:true env sigma c
  with RetypeError e ->
    user_err
      (str "Cannot reinterpret " ++ Id.print src ++ str " bound to " ++
       quote (Termops.Internal.print_constr_env env sigma c) ++
       str " in the current environment" ++ spc() ++
       surround (print_retype_error e))

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

let relevance_of_projection_repr env (p, u) =
  ERelevance.make @@ Relevanceops.relevance_of_projection_repr env (p, EConstr.Unsafe.to_instance u)

let relevance_of_term env sigma c =
  if Environ.sprop_allowed env then
    let rec aux rels c =
      match kind sigma c with
      | Rel n ->
        let len = Range.length rels in
        if n <= len then Range.get rels (n - 1)
        else ERelevance.make @@ Relevanceops.relevance_of_rel env (n - len)
      | Var x -> ERelevance.make @@ Relevanceops.relevance_of_var env x
      | Sort _ -> ERelevance.relevant
      | Cast (c, _, _) -> aux rels c
      | Prod _ -> ERelevance.relevant
      | Lambda ({binder_relevance=r}, _, bdy) ->
        aux (Range.cons r rels) bdy
      | LetIn ({binder_relevance=r}, _, _, bdy) ->
        aux (Range.cons r rels) bdy
      | App (c, _) -> aux rels c
      | Const (c,u) ->
        let u = Unsafe.to_instance u in
        ERelevance.make @@ Relevanceops.relevance_of_constant env (c,u)
      | Ind _ -> ERelevance.relevant
      | Construct (c,u) ->
        let u = Unsafe.to_instance u in
        ERelevance.make @@ Relevanceops.relevance_of_constructor env (c,u)
      | Case (_, _, _, (_, r), _, _, _) -> r
      | Fix ((_,i),(lna,_,_)) -> (lna.(i)).binder_relevance
      | CoFix (i,(lna,_,_)) -> (lna.(i)).binder_relevance
      | Proj (p, r, _) -> r
      | Evar (evk, _) ->
          let evi = Evd.find_undefined sigma evk in
          Evd.evar_relevance evi
      | Int _ | Float _ | String _ | Array _ -> ERelevance.relevant
      | Meta _ -> ERelevance.relevant
    in
    aux Range.empty c
  else ERelevance.relevant

let is_term_irrelevant env sigma c =
  let r = relevance_of_term env sigma c in
  Evd.is_relevance_irrelevant sigma r

let relevance_of_type env sigma t =
  let s = get_sort_of env sigma t in
  ESorts.relevance_of_sort s

let relevance_of_sort = ESorts.relevance_of_sort

let relevance_of_sort_family sigma f = ERelevance.make (Sorts.relevance_of_sort_family f)
