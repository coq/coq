(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module CVars = Vars

open Pp
open CErrors
open Util
open Term
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

let push_rec_types pfix env =
  let (i, c, t) = pfix in
  let inj c = EConstr.Unsafe.to_constr c in
  push_rec_types (i, Array.map inj c, Array.map inj t) env

let meta_type evd mv =
  let ty =
    try Evd.meta_ftype evd mv
    with Not_found -> anomaly (str "unknown meta ?" ++ str (Nameops.string_of_meta mv)) in
  let ty = Evd.map_fl EConstr.of_constr ty in
  meta_instance evd ty

let constant_type_knowing_parameters env sigma (cst, u) jl =
  let u = Unsafe.to_instance u in
  let paramstyp = Array.map (fun j -> lazy (EConstr.to_constr sigma j.uj_type)) jl in
  EConstr.of_constr (type_of_constant_knowing_parameters_in env (cst, u) paramstyp)

let inductive_type_knowing_parameters env sigma (ind,u) jl =
  let u = Unsafe.to_instance u in
  let mspec = lookup_mind_specif env ind in
  let paramstyp = Array.map (fun j -> lazy (EConstr.to_constr sigma j.uj_type)) jl in
  EConstr.of_constr (Inductive.type_of_inductive_knowing_parameters env (mspec,u) paramstyp)

let e_type_judgment env evdref j =
  match EConstr.kind !evdref (whd_all env !evdref j.uj_type) with
    | Sort s -> {utj_val = j.uj_val; utj_type = ESorts.kind !evdref s }
    | Evar ev ->
        let (evd,s) = Evardefine.define_evar_as_sort env !evdref ev in
        evdref := evd; { utj_val = j.uj_val; utj_type = s }
    | _ -> error_not_a_type env !evdref j

let e_assumption_of_judgment env evdref j =
  try (e_type_judgment env evdref j).utj_val
  with Type_errors.TypeError _ | PretypeError _ ->
    error_assumption env !evdref j

let e_judge_of_apply env evdref funj argjv =
  let rec apply_rec n typ = function
  | [] ->
      { uj_val  = mkApp (j_val funj, Array.map j_val argjv);
        uj_type = typ }
  | hj::restjl ->
      match EConstr.kind !evdref (whd_all env !evdref typ) with
      | Prod (_,c1,c2) ->
	 if Evarconv.e_cumul env evdref hj.uj_type c1 then
	   apply_rec (n+1) (subst1 hj.uj_val c2) restjl
	 else
	   error_cant_apply_bad_type env !evdref (n, c1, hj.uj_type) funj argjv
      | Evar ev ->
	  let (evd',t) = Evardefine.define_evar_as_product !evdref ev in
          evdref := evd';
          let (_,_,c2) = destProd evd' t in
	  apply_rec (n+1) (subst1 hj.uj_val c2) restjl
      | _ ->
	  error_cant_apply_not_functional env !evdref funj argjv
  in
  apply_rec 1 funj.uj_type (Array.to_list argjv)

let e_check_branch_types env evdref (ind,u) cj (lfj,explft) =
  if not (Int.equal (Array.length lfj) (Array.length explft)) then
    error_number_branches env !evdref cj (Array.length explft);
  for i = 0 to Array.length explft - 1 do
    if not (Evarconv.e_cumul env evdref lfj.(i).uj_type explft.(i)) then
      error_ill_formed_branch env !evdref cj.uj_val ((ind,i+1),u) lfj.(i).uj_type explft.(i)
  done

let max_sort l =
  if Sorts.List.mem InType l then InType else
  if Sorts.List.mem InSet l then InSet else InProp

let e_is_correct_arity env evdref c pj ind specif params =
  let arsign = make_arity_signature env !evdref true (make_ind_family (ind,params)) in
  let allowed_sorts = elim_sorts specif in
  let error () = Pretype_errors.error_elim_arity env !evdref ind allowed_sorts c pj None in
  let rec srec env pt ar =
    let pt' = whd_all env !evdref pt in
    match EConstr.kind !evdref pt', ar with
    | Prod (na1,a1,t), (LocalAssum (_,a1'))::ar' ->
        if not (Evarconv.e_cumul env evdref a1 a1') then error ();
        srec (push_rel (LocalAssum (na1,a1)) env) t ar'
    | Sort s, [] ->
        let s = ESorts.kind !evdref s in
        if not (Sorts.List.mem (Sorts.family s) allowed_sorts)
        then error ()
    | Evar (ev,_), [] ->
        let evd, s = Evd.fresh_sort_in_family env !evdref (max_sort allowed_sorts) in
        evdref := Evd.define ev (Constr.mkSort s) evd
    | _, (LocalDef _ as d)::ar' ->
        srec (push_rel d env) (lift 1 pt') ar'
    | _ ->
        error ()
  in
  srec env pj.uj_type (List.rev arsign)

let lambda_applist_assum sigma n c l =
  let rec app n subst t l =
    if Int.equal n 0 then
      if l == [] then substl subst t
      else anomaly (Pp.str "Not enough arguments")
    else match EConstr.kind sigma t, l with
    | Lambda(_,_,c), arg::l -> app (n-1) (arg::subst) c l
    | LetIn(_,b,_,c), _ -> app (n-1) (substl subst b::subst) c l
    | _ -> anomaly (Pp.str "Not enough lambda/let's") in
  app n [] c l

let e_type_case_branches env evdref (ind,largs) pj c =
  let specif = lookup_mind_specif env (fst ind) in
  let nparams = inductive_params specif in
  let (params,realargs) = List.chop nparams largs in
  let p = pj.uj_val in
  let params = List.map EConstr.Unsafe.to_constr params in
  let () = e_is_correct_arity env evdref c pj ind specif params in
  let lc = build_branches_type ind specif params (EConstr.to_constr !evdref p) in
  let lc = Array.map EConstr.of_constr lc in
  let n = (snd specif).Declarations.mind_nrealdecls in
  let ty = whd_betaiota !evdref (lambda_applist_assum !evdref (n+1) p (realargs@[c])) in
  (lc, ty)

let e_judge_of_case env evdref ci pj cj lfj =
  let ((ind, u), spec) =
    try find_mrectype env !evdref cj.uj_type
    with Not_found -> error_case_not_inductive env !evdref cj in
  let indspec = ((ind, EInstance.kind !evdref u), spec) in
  let _ = check_case_info env (fst indspec) ci in
  let (bty,rslty) = e_type_case_branches env evdref indspec pj cj.uj_val in
  e_check_branch_types env evdref (fst indspec) cj (lfj,bty);
  { uj_val  = mkCase (ci, pj.uj_val, cj.uj_val, Array.map j_val lfj);
    uj_type = rslty }

let check_type_fixpoint ?loc env evdref lna lar vdefj =
  let lt = Array.length vdefj in
    if Int.equal (Array.length lar) lt then
      for i = 0 to lt-1 do
        if not (Evarconv.e_cumul env evdref (vdefj.(i)).uj_type
		  (lift lt lar.(i))) then
          error_ill_typed_rec_body ?loc env !evdref
            i lna vdefj lar
      done

(* FIXME: might depend on the level of actual parameters!*)
let check_allowed_sort env sigma ind c p =
  let pj = Retyping.get_judgment_of env sigma p in
  let ksort = family_of_sort (ESorts.kind sigma (sort_of_arity env sigma pj.uj_type)) in
  let specif = Global.lookup_inductive (fst ind) in
  let sorts = elim_sorts specif in
  if not (List.exists ((==) ksort) sorts) then
    let s = inductive_sort_family (snd specif) in
    error_elim_arity env sigma ind sorts c pj
      (Some(ksort,s,Type_errors.error_elim_explain ksort s))

let e_judge_of_cast env evdref cj k tj =
  let expected_type = tj.utj_val in
  if not (Evarconv.e_cumul env evdref cj.uj_type expected_type) then
    error_actual_type_core env !evdref cj expected_type;
  { uj_val = mkCast (cj.uj_val, k, expected_type);
    uj_type = expected_type }

let enrich_env env evdref =
  let penv = Environ.pre_env env in
  let penv' = Pre_env.({ penv with env_stratification =
    { penv.env_stratification with env_universes = Evd.universes !evdref } }) in
  Environ.env_of_pre_env penv'

let check_fix env sigma pfix =
  let inj c = EConstr.to_constr sigma c in
  let (idx, (ids, cs, ts)) = pfix in
  check_fix env (idx, (ids, Array.map inj cs, Array.map inj ts))

let check_cofix env sigma pcofix =
  let inj c = EConstr.to_constr sigma c in
  let (idx, (ids, cs, ts)) = pcofix in
  check_cofix env (idx, (ids, Array.map inj cs, Array.map inj ts))

(* The typing machine with universes and existential variables. *)

let judge_of_prop =
  { uj_val = EConstr.mkProp;
    uj_type = EConstr.mkSort type1_sort }

let judge_of_set =
  { uj_val = EConstr.mkSet;
    uj_type = EConstr.mkSort type1_sort }

let judge_of_prop_contents = function
  | Null -> judge_of_prop
  | Pos -> judge_of_set

let judge_of_type u =
  let uu = Univ.Universe.super u in
    { uj_val = EConstr.mkType u;
      uj_type = EConstr.mkType uu }

let judge_of_relative env v =
  Termops.on_judgment EConstr.of_constr (judge_of_relative env v)

let judge_of_variable env id =
  Termops.on_judgment EConstr.of_constr (judge_of_variable env id)

let judge_of_projection env sigma p cj =
  let pb = lookup_projection p env in
  let (ind,u), args =
    try find_mrectype env sigma cj.uj_type
    with Not_found -> error_case_not_inductive env sigma cj
  in
  let u = EInstance.kind sigma u in
    let ty = EConstr.of_constr (CVars.subst_instance_constr u pb.Declarations.proj_type) in
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

(* cstr must be in n.f. w.r.t. evars and execute returns a judgement
   where both the term and type are in n.f. *)
let rec execute env evdref cstr =
  let cstr = whd_evar !evdref cstr in
  match EConstr.kind !evdref cstr with
    | Meta n ->
        { uj_val = cstr; uj_type = meta_type !evdref n }

    | Evar ev ->
	let ty = EConstr.existential_type !evdref ev in
	let jty = execute env evdref ty in
	let jty = e_assumption_of_judgment env evdref jty in
	{ uj_val = cstr; uj_type = jty }

    | Rel n ->
	judge_of_relative env n

    | Var id ->
        judge_of_variable env id

    | Const (c, u) ->
        let u = EInstance.kind !evdref u in
        make_judge cstr (EConstr.of_constr (rename_type_of_constant env (c, u)))

    | Ind (ind, u) ->
        let u = EInstance.kind !evdref u in
	make_judge cstr (EConstr.of_constr (rename_type_of_inductive env (ind, u)))

    | Construct (cstruct, u) ->
        let u = EInstance.kind !evdref u in
	make_judge cstr (EConstr.of_constr (rename_type_of_constructor env (cstruct, u)))

    | Case (ci,p,c,lf) ->
        let cj = execute env evdref c in
        let pj = execute env evdref p in
        let lfj = execute_array env evdref lf in
        e_judge_of_case env evdref ci pj cj lfj

    | Fix ((vn,i as vni),recdef) ->
        let (_,tys,_ as recdef') = execute_recdef env evdref recdef in
	let fix = (vni,recdef') in
        check_fix env !evdref fix;
	make_judge (mkFix fix) tys.(i)

    | CoFix (i,recdef) ->
        let (_,tys,_ as recdef') = execute_recdef env evdref recdef in
        let cofix = (i,recdef') in
        check_cofix env !evdref cofix;
	make_judge (mkCoFix cofix) tys.(i)

    | Sort s ->
      begin match ESorts.kind !evdref s with
      | Prop c ->
        judge_of_prop_contents c
      | Type u ->
        judge_of_type u
      end

    | Proj (p, c) -> 
        let cj = execute env evdref c in
	  judge_of_projection env !evdref p cj

    | App (f,args) ->
        let jl = execute_array env evdref args in
	let j =
	  match EConstr.kind !evdref f with
	    | Ind (ind, u) when EInstance.is_empty u && Environ.template_polymorphic_ind ind env ->
		make_judge f
		  (inductive_type_knowing_parameters env !evdref (ind, u) jl)
	    | Const (cst, u) when EInstance.is_empty u && Environ.template_polymorphic_constant cst env ->
		make_judge f
		  (constant_type_knowing_parameters env !evdref (cst, u) jl)
	    | _ ->
                (* No template polymorphism *)
		execute env evdref f
	in
	e_judge_of_apply env evdref j jl

    | Lambda (name,c1,c2) ->
        let j = execute env evdref c1 in
	let var = e_type_judgment env evdref j in
	let env1 = push_rel (LocalAssum (name, var.utj_val)) env in
        let j' = execute env1 evdref c2 in
        judge_of_abstraction env1 name var j'

    | Prod (name,c1,c2) ->
        let j = execute env evdref c1 in
        let varj = e_type_judgment env evdref j in
	let env1 = push_rel (LocalAssum (name, varj.utj_val)) env in
        let j' = execute env1 evdref c2 in
        let varj' = e_type_judgment env1 evdref j' in
	judge_of_product env name varj varj'

     | LetIn (name,c1,c2,c3) ->
        let j1 = execute env evdref c1 in
        let j2 = execute env evdref c2 in
        let j2 = e_type_judgment env evdref j2 in
        let _ =  e_judge_of_cast env evdref j1 DEFAULTcast j2 in
        let env1 = push_rel (LocalDef (name, j1.uj_val, j2.utj_val)) env in
        let j3 = execute env1 evdref c3 in
        judge_of_letin env name j1 j2 j3

    | Cast (c,k,t) ->
        let cj = execute env evdref c in
        let tj = execute env evdref t in
	let tj = e_type_judgment env evdref tj in
        e_judge_of_cast env evdref cj k tj

and execute_recdef env evdref (names,lar,vdef) =
  let larj = execute_array env evdref lar in
  let lara = Array.map (e_assumption_of_judgment env evdref) larj in
  let env1 = push_rec_types (names,lara,vdef) env in
  let vdefj = execute_array env1 evdref vdef in
  let vdefv = Array.map j_val vdefj in
  let _ = check_type_fixpoint env1 evdref names lara vdefj in
  (names,lara,vdefv)

and execute_array env evdref = Array.map (execute env evdref)

let e_check env evdref c t =
  let env = enrich_env env evdref in
  let j = execute env evdref c in
  if not (Evarconv.e_cumul env evdref j.uj_type t) then
    error_actual_type_core env !evdref j t

(* Type of a constr *)

let unsafe_type_of env evd c =
  let evdref = ref evd in
  let env = enrich_env env evdref in
  let j = execute env evdref c in
    j.uj_type

(* Sort of a type *)

let e_sort_of env evdref c =
  let env = enrich_env env evdref in
  let j = execute env evdref c in
  let a = e_type_judgment env evdref j in
  a.utj_type

(* Try to solve the existential variables by typing *)

let type_of ?(refresh=false) env evd c =
  let evdref = ref evd in
  let env = enrich_env env evdref in
  let j = execute env evdref c in
  (* side-effect on evdref *)
    if refresh then
      Evarsolve.refresh_universes ~onlyalg:true (Some false) env !evdref j.uj_type
    else !evdref, j.uj_type

let e_type_of ?(refresh=false) env evdref c =
  let env = enrich_env env evdref in
  let j = execute env evdref c in
  (* side-effect on evdref *)
    if refresh then
      let evd, c = Evarsolve.refresh_universes ~onlyalg:true (Some false) env !evdref j.uj_type in
      let () = evdref := evd in
      c
    else j.uj_type

let e_solve_evars env evdref c =
  let env = enrich_env env evdref in
  let c = (execute env evdref c).uj_val in
  (* side-effect on evdref *)
  nf_evar !evdref c

let _ = Evarconv.set_solve_evars (fun env evdref c -> e_solve_evars env evdref c)
