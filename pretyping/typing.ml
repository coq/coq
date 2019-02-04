(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
open Environ
open EConstr
open Vars
open Reductionops
open Inductive
open Inductiveops
open Typeops
open Arguments_renaming
open Pretype_errors
open Context.Rel.Declaration

let meta_type evd mv =
  let ty =
    try Evd.meta_ftype evd mv
    with Not_found -> anomaly (str "unknown meta ?" ++ str (Nameops.string_of_meta mv) ++ str ".") in
  meta_instance evd ty

let inductive_type_knowing_parameters env sigma (ind,u) jl =
  let u = Unsafe.to_instance u in
  let mspec = lookup_mind_specif env ind in
  let paramstyp = Array.map (fun j -> lazy (EConstr.to_constr ~abort_on_undefined_evars:false sigma j.uj_type)) jl in
  Inductive.type_of_inductive_knowing_parameters env (mspec,u) paramstyp

let type_judgment env sigma j =
  match EConstr.kind sigma (whd_all env sigma j.uj_type) with
    | Sort s -> sigma, {utj_val = j.uj_val; utj_type = ESorts.kind sigma s }
    | Evar ev ->
        let (sigma,s) = Evardefine.define_evar_as_sort env sigma ev in
        sigma, { utj_val = j.uj_val; utj_type = s }
    | _ -> error_not_a_type env sigma j

let assumption_of_judgment env sigma j =
  try
    let sigma, j = type_judgment env sigma j in
    sigma, j.utj_val
  with Type_errors.TypeError _ | PretypeError _ ->
    error_assumption env sigma j

let judge_of_applied_inductive_knowing_parameters env sigma funj ind argjv =
  let rec apply_rec sigma n typ = function
  | [] ->
      sigma, { uj_val  = mkApp (j_val funj, Array.map j_val argjv);
               uj_type =
                 let ar = inductive_type_knowing_parameters env sigma ind argjv in
                 hnf_prod_appvect env sigma (EConstr.of_constr ar) (Array.map j_val argjv) }
  | hj::restjl ->
       let sigma, (c1,c2) =
         match EConstr.kind sigma (whd_all env sigma typ) with
         | Prod (_,c1,c2) -> sigma, (c1,c2)
         | Evar ev ->
             let (sigma,t) = Evardefine.define_evar_as_product sigma ev in
             let (_,c1,c2) = destProd sigma t in
             sigma, (c1,c2)
         | _ ->
             error_cant_apply_not_functional env sigma funj argjv
       in
       begin match Evarconv.cumul env sigma hj.uj_type c1 with
         | Some sigma ->
           apply_rec sigma (n+1) (subst1 hj.uj_val c2) restjl
         | None ->
           error_cant_apply_bad_type env sigma (n, c1, hj.uj_type) funj argjv
       end
  in
  apply_rec sigma 1 funj.uj_type (Array.to_list argjv)

let judge_of_apply env sigma funj argjv =
  let rec apply_rec sigma n typ = function
  | [] ->
    sigma, { uj_val  = mkApp (j_val funj, Array.map j_val argjv);
             uj_type = typ }
  | hj::restjl ->
       let sigma, (c1,c2) =
         match EConstr.kind sigma (whd_all env sigma typ) with
         | Prod (_,c1,c2) -> sigma, (c1,c2)
         | Evar ev ->
             let (sigma,t) = Evardefine.define_evar_as_product sigma ev in
             let (_,c1,c2) = destProd sigma t in
             sigma, (c1,c2)
         | _ ->
            error_cant_apply_not_functional env sigma funj argjv
       in
       begin match Evarconv.cumul env sigma hj.uj_type c1 with
         | Some sigma ->
           apply_rec sigma (n+1) (subst1 hj.uj_val c2) restjl
         | None ->
           error_cant_apply_bad_type env sigma (n, c1, hj.uj_type) funj argjv
       end
  in
  apply_rec sigma 1 funj.uj_type (Array.to_list argjv)

let check_branch_types env sigma (ind,u) cj (lfj,explft) =
  if not (Int.equal (Array.length lfj) (Array.length explft)) then
    error_number_branches env sigma cj (Array.length explft);
  Array.fold_left2_i (fun i sigma lfj explft ->
      match Evarconv.cumul env sigma lfj.uj_type explft with
      | Some sigma -> sigma
      | None ->
        error_ill_formed_branch env sigma cj.uj_val ((ind,i+1),u) lfj.uj_type explft)
    sigma lfj explft

let max_sort l =
  if Sorts.List.mem InType l then InType else
  if Sorts.List.mem InSet l then InSet else InProp

let is_correct_arity env sigma c pj ind specif params =
  let arsign = make_arity_signature env sigma true (make_ind_family (ind,params)) in
  let allowed_sorts = elim_sorts specif in
  let error () = Pretype_errors.error_elim_arity env sigma ind allowed_sorts c pj None in
  let rec srec env sigma pt ar =
    let pt' = whd_all env sigma pt in
    match EConstr.kind sigma pt', ar with
    | Prod (na1,a1,t), (LocalAssum (_,a1'))::ar' ->
      begin match Evarconv.cumul env sigma a1 a1' with
        | None -> error ()
        | Some sigma ->
          srec (push_rel (LocalAssum (na1,a1)) env) sigma t ar'
      end
    | Sort s, [] ->
        let s = ESorts.kind sigma s in
        if not (Sorts.List.mem (Sorts.family s) allowed_sorts)
        then error ()
        else sigma
    | Evar (ev,_), [] ->
        let sigma, s = Evd.fresh_sort_in_family sigma (max_sort allowed_sorts) in
        let sigma = Evd.define ev (mkSort s) sigma in
        sigma
    | _, (LocalDef _ as d)::ar' ->
        srec (push_rel d env) sigma (lift 1 pt') ar'
    | _ ->
        error ()
  in
  srec env sigma pj.uj_type (List.rev arsign)

let lambda_applist_assum sigma n c l =
  let rec app n subst t l =
    if Int.equal n 0 then
      if l == [] then substl subst t
      else anomaly (Pp.str "Not enough arguments.")
    else match EConstr.kind sigma t, l with
    | Lambda(_,_,c), arg::l -> app (n-1) (arg::subst) c l
    | LetIn(_,b,_,c), _ -> app (n-1) (substl subst b::subst) c l
    | _ -> anomaly (Pp.str "Not enough lambda/let's.") in
  app n [] c l

let type_case_branches env sigma (ind,largs) pj c =
  let specif = lookup_mind_specif env (fst ind) in
  let nparams = inductive_params specif in
  let (params,realargs) = List.chop nparams largs in
  let p = pj.uj_val in
  let params = List.map EConstr.Unsafe.to_constr params in
  let sigma = is_correct_arity env sigma c pj ind specif params in
  let lc = build_branches_type ind specif params (EConstr.to_constr ~abort_on_undefined_evars:false sigma p) in
  let lc = Array.map EConstr.of_constr lc in
  let n = (snd specif).Declarations.mind_nrealdecls in
  let ty = whd_betaiota sigma (lambda_applist_assum sigma (n+1) p (realargs@[c])) in
  sigma, (lc, ty)

let judge_of_case env sigma ci pj cj lfj =
  let ((ind, u), spec) =
    try find_mrectype env sigma cj.uj_type
    with Not_found -> error_case_not_inductive env sigma cj in
  let indspec = ((ind, EInstance.kind sigma u), spec) in
  let _ = check_case_info env (fst indspec) ci in
  let sigma, (bty,rslty) = type_case_branches env sigma indspec pj cj.uj_val in
  let sigma = check_branch_types env sigma (fst indspec) cj (lfj,bty) in
  sigma, { uj_val  = mkCase (ci, pj.uj_val, cj.uj_val, Array.map j_val lfj);
           uj_type = rslty }

let check_type_fixpoint ?loc env sigma lna lar vdefj =
  let lt = Array.length vdefj in
  assert (Int.equal (Array.length lar) lt);
  Array.fold_left2_i (fun i sigma defj ar ->
      match Evarconv.cumul env sigma defj.uj_type (lift lt ar) with
      | Some sigma -> sigma
      | None ->
        error_ill_typed_rec_body ?loc env sigma
          i lna vdefj lar)
    sigma vdefj lar


(* FIXME: might depend on the level of actual parameters!*)
let check_allowed_sort env sigma ind c p =
  let specif = Global.lookup_inductive (fst ind) in
  let sorts = elim_sorts specif in
  let pj = Retyping.get_judgment_of env sigma p in
  let _, s = splay_prod env sigma pj.uj_type in
  let ksort = match EConstr.kind sigma s with
  | Sort s -> Sorts.family (ESorts.kind sigma s)
  | _ -> error_elim_arity env sigma ind sorts c pj None in
  if not (List.exists ((==) ksort) sorts) then
    let s = inductive_sort_family (snd specif) in
    error_elim_arity env sigma ind sorts c pj
      (Some(ksort,s,Type_errors.error_elim_explain ksort s))

let judge_of_cast env sigma cj k tj =
  let expected_type = tj.utj_val in
  match Evarconv.cumul env sigma cj.uj_type expected_type with
  | None ->
    error_actual_type_core env sigma cj expected_type;
  | Some sigma ->
    sigma, { uj_val = mkCast (cj.uj_val, k, expected_type);
             uj_type = expected_type }

let check_fix env sigma pfix =
  let inj c = EConstr.to_constr ~abort_on_undefined_evars:false sigma c in
  let (idx, (ids, cs, ts)) = pfix in
  check_fix env (idx, (ids, Array.map inj cs, Array.map inj ts))

let check_cofix env sigma pcofix =
  let inj c = EConstr.to_constr sigma c in
  let (idx, (ids, cs, ts)) = pcofix in
  check_cofix env (idx, (ids, Array.map inj cs, Array.map inj ts))

(* The typing machine with universes and existential variables. *)

let judge_of_prop =
  { uj_val = EConstr.mkProp;
    uj_type = EConstr.mkSort Sorts.type1 }

let judge_of_set =
  { uj_val = EConstr.mkSet;
    uj_type = EConstr.mkSort Sorts.type1 }

let judge_of_type u =
  let uu = Univ.Universe.super u in
    { uj_val = EConstr.mkType u;
      uj_type = EConstr.mkType uu }

let judge_of_relative env v =
  Termops.on_judgment EConstr.of_constr (judge_of_relative env v)

let judge_of_variable env id =
  Termops.on_judgment EConstr.of_constr (judge_of_variable env id)

let judge_of_projection env sigma p cj =
  let pty = lookup_projection p env in
  let (ind,u), args =
    try find_mrectype env sigma cj.uj_type
    with Not_found -> error_case_not_inductive env sigma cj
  in
  let u = EInstance.kind sigma u in
  let ty = EConstr.of_constr (CVars.subst_instance_constr u pty) in
  let ty = substl (cj.uj_val :: List.rev args) ty in
  {uj_val = EConstr.mkProj (p,cj.uj_val);
   uj_type = ty}

let judge_of_abstraction env name var j =
  { uj_val = mkLambda (name, var.utj_val, j.uj_val);
    uj_type = mkProd (name, var.utj_val, j.uj_type) }

let judge_of_product env name t1 t2 =
  let s = sort_of_product env t1.utj_type t2.utj_type in
  { uj_val = mkProd (name, t1.utj_val, t2.utj_val);
    uj_type = mkSort s }

let judge_of_letin env name defj typj j =
  { uj_val = mkLetIn (name, defj.uj_val, typj.utj_val, j.uj_val) ;
    uj_type = subst1 defj.uj_val j.uj_type }

let check_hyps_inclusion env sigma f x hyps =
  let evars = Evarutil.safe_evar_value sigma, Evd.universes sigma in
  let f x = EConstr.Unsafe.to_constr (f x) in
  Typeops.check_hyps_inclusion env ~evars f x hyps

let type_of_constant env sigma (c,u) =
  let open Declarations in
  let cb = Environ.lookup_constant c env in
  let () = check_hyps_inclusion env sigma mkConstU (c,u) cb.const_hyps in
  let u = EInstance.kind sigma u in
  let ty, csts = Environ.constant_type env (c,u) in
  let sigma = Evd.add_constraints sigma csts in
  sigma, (EConstr.of_constr (rename_type ty (Names.GlobRef.ConstRef c)))

let type_of_inductive env sigma (ind,u) =
  let open Declarations in
  let (mib,_ as specif) = Inductive.lookup_mind_specif env ind in
  let () = check_hyps_inclusion env sigma mkIndU (ind,u) mib.mind_hyps in
  let u = EInstance.kind sigma u in
  let ty, csts = Inductive.constrained_type_of_inductive env (specif,u) in
  let sigma = Evd.add_constraints sigma csts in
  sigma, (EConstr.of_constr (rename_type ty (Names.GlobRef.IndRef ind)))

let type_of_constructor env sigma ((ind,_ as ctor),u) =
  let open Declarations in
  let (mib,_ as specif) = Inductive.lookup_mind_specif env ind in
  let () = check_hyps_inclusion env sigma mkIndU (ind,u) mib.mind_hyps in
  let u = EInstance.kind sigma u in
  let ty, csts = Inductive.constrained_type_of_constructor (ctor,u) specif in
  let sigma = Evd.add_constraints sigma csts in
  sigma, (EConstr.of_constr (rename_type ty (Names.GlobRef.ConstructRef ctor)))

let judge_of_int env v =
  Termops.on_judgment EConstr.of_constr (judge_of_int env v)

(* cstr must be in n.f. w.r.t. evars and execute returns a judgement
   where both the term and type are in n.f. *)
let rec execute env sigma cstr =
  let cstr = whd_evar sigma cstr in
  match EConstr.kind sigma cstr with
    | Meta n ->
        sigma, { uj_val = cstr; uj_type = meta_type sigma n }

    | Evar ev ->
        let ty = EConstr.existential_type sigma ev in
        let sigma, jty = execute env sigma ty in
        let sigma, jty = assumption_of_judgment env sigma jty in
        sigma, { uj_val = cstr; uj_type = jty }

    | Rel n ->
        sigma, judge_of_relative env n

    | Var id ->
        sigma, judge_of_variable env id

    | Const c ->
        let sigma, ty = type_of_constant env sigma c in
        sigma, make_judge cstr ty

    | Ind ind ->
        let sigma, ty = type_of_inductive env sigma ind in
        sigma, make_judge cstr ty

    | Construct ctor ->
        let sigma, ty = type_of_constructor env sigma ctor in
        sigma, make_judge cstr ty

    | Case (ci,p,c,lf) ->
        let sigma, cj = execute env sigma c in
        let sigma, pj = execute env sigma p in
        let sigma, lfj = execute_array env sigma lf in
        judge_of_case env sigma ci pj cj lfj

    | Fix ((vn,i as vni),recdef) ->
        let sigma, (_,tys,_ as recdef') = execute_recdef env sigma recdef in
	let fix = (vni,recdef') in
        check_fix env sigma fix;
        sigma, make_judge (mkFix fix) tys.(i)

    | CoFix (i,recdef) ->
        let sigma, (_,tys,_ as recdef') = execute_recdef env sigma recdef in
        let cofix = (i,recdef') in
        check_cofix env sigma cofix;
        sigma, make_judge (mkCoFix cofix) tys.(i)

    | Sort s ->
      begin match ESorts.kind sigma s with
        | Prop -> sigma, judge_of_prop
        | Set -> sigma, judge_of_set
        | Type u -> sigma, judge_of_type u
      end

    | Proj (p, c) -> 
      let sigma, cj = execute env sigma c in
      sigma, judge_of_projection env sigma p cj

    | App (f,args) ->
        let sigma, jl = execute_array env sigma args in
        (match EConstr.kind sigma f with
            | Ind (ind, u) when EInstance.is_empty u && Environ.template_polymorphic_ind ind env ->
               let sigma, fj = execute env sigma f in
               judge_of_applied_inductive_knowing_parameters env sigma fj (ind, u) jl
            | _ ->
               (* No template polymorphism *)
               let sigma, fj = execute env sigma f in
               judge_of_apply env sigma fj jl)

    | Lambda (name,c1,c2) ->
        let sigma, j = execute env sigma c1 in
        let sigma, var = type_judgment env sigma j in
	let env1 = push_rel (LocalAssum (name, var.utj_val)) env in
        let sigma, j' = execute env1 sigma c2 in
        sigma, judge_of_abstraction env1 name var j'

    | Prod (name,c1,c2) ->
        let sigma, j = execute env sigma c1 in
        let sigma, varj = type_judgment env sigma j in
	let env1 = push_rel (LocalAssum (name, varj.utj_val)) env in
        let sigma, j' = execute env1 sigma c2 in
        let sigma, varj' = type_judgment env1 sigma j' in
        sigma, judge_of_product env name varj varj'

     | LetIn (name,c1,c2,c3) ->
        let sigma, j1 = execute env sigma c1 in
        let sigma, j2 = execute env sigma c2 in
        let sigma, j2 = type_judgment env sigma j2 in
        let sigma, _ =  judge_of_cast env sigma j1 DEFAULTcast j2 in
        let env1 = push_rel (LocalDef (name, j1.uj_val, j2.utj_val)) env in
        let sigma, j3 = execute env1 sigma c3 in
        sigma, judge_of_letin env name j1 j2 j3

    | Cast (c,k,t) ->
        let sigma, cj = execute env sigma c in
        let sigma, tj = execute env sigma t in
        let sigma, tj = type_judgment env sigma tj in
        judge_of_cast env sigma cj k tj

    | Int i ->
        sigma, judge_of_int env i

and execute_recdef env sigma (names,lar,vdef) =
  let sigma, larj = execute_array env sigma lar in
  let sigma, lara = Array.fold_left_map (assumption_of_judgment env) sigma larj in
  let env1 = push_rec_types (names,lara,vdef) env in
  let sigma, vdefj = execute_array env1 sigma vdef in
  let vdefv = Array.map j_val vdefj in
  let sigma = check_type_fixpoint env1 sigma names lara vdefj in
  sigma, (names,lara,vdefv)

and execute_array env = Array.fold_left_map (execute env)

let check env sigma c t =
  let sigma, j = execute env sigma c in
  match Evarconv.cumul env sigma j.uj_type t with
  | None ->
    error_actual_type_core env sigma j t
  | Some sigma -> sigma

(* Type of a constr *)

let unsafe_type_of env sigma c =
  let sigma, j = execute env sigma c in
  j.uj_type

(* Sort of a type *)

let sort_of env sigma c =
  let sigma, j = execute env sigma c in
  let sigma, a = type_judgment env sigma j in
  sigma, a.utj_type

(* Try to solve the existential variables by typing *)

let type_of ?(refresh=false) env sigma c =
  let sigma, j = execute env sigma c in
  (* side-effect on evdref *)
    if refresh then
      Evarsolve.refresh_universes ~onlyalg:true (Some false) env sigma j.uj_type
    else sigma, j.uj_type

let solve_evars env sigma c =
  let sigma, j = execute env sigma c in
  (* side-effect on evdref *)
  sigma, nf_evar sigma j.uj_val

let _ = Evarconv.set_solve_evars (fun env sigma c -> solve_evars env sigma c)
