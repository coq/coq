
(* $Id$ *)

open Pp
open Util
open Names
open Univ
(*i open Generic i*)
open Term
open Reduction
open Sign
open Declarations
open Inductive
open Environ
open Type_errors
open Typeops
open Indtypes

type judgment = unsafe_judgment

let j_val j = j.uj_val
let j_type j = body_of_type j.uj_type

let vect_lift = Array.mapi lift
let vect_lift_type = Array.mapi (fun i t -> typed_app (lift i) t)

(*s The machine flags. 
   [fix] indicates if we authorize general fixpoints ($\mathit{recarg} < 0$)
   like [Acc_rec.fw].
   [nocheck] indicates if we can skip some verifications to accelerate
   the type inference. *)

type 'a mach_flags = {
  fix : bool;
  nocheck : bool }

(* The typing machine without information. *)

let rec execute mf env cstr =
  let cst0 = Constraint.empty in
  match kind_of_term cstr with
    | IsMeta _ ->
	anomaly "the kernel does not understand metas"
    | IsEvar _ ->
	anomaly "the kernel does not understand existential variables"
	
    | IsRel n -> 
	(relative env Evd.empty n, cst0)

    | IsVar id -> 
	(make_judge cstr (lookup_var_type id env), cst0)

    (* ATTENTION : faudra faire le typage du contexte des Const,
    MutInd et MutConstructsi un jour cela devient des constructions
    arbitraires et non plus des variables *)

    | IsConst c ->
        (make_judge cstr (type_of_constant env Evd.empty c), cst0)
	  
    | IsMutInd ind ->
	(make_judge cstr (type_of_inductive env Evd.empty ind), cst0)
	  
    | IsMutConstruct c -> 
	(make_judge cstr (type_of_constructor env Evd.empty c), cst0)
	  
    | IsMutCase (ci,p,c,lf) ->
        let (cj,cst1) = execute mf env c in
        let (pj,cst2) = execute mf env p in
        let (lfj,cst3) = execute_array mf env lf in
	let cst = Constraint.union cst1 (Constraint.union cst2 cst3) in
        (type_of_case env Evd.empty ci pj cj lfj, cst)
  
    | IsFix ((vn,i as vni),(lar,lfi,vdef)) ->
        if (not mf.fix) && array_exists (fun n -> n < 0) vn then
          error "General Fixpoints not allowed";
        let (larjv,vdefv,cst) = execute_fix mf env lar lfi vdef in
	let larv = Array.map body_of_type larjv in
        let fix = (vni,(larv,lfi,vdefv)) in
        check_fix env Evd.empty fix;
	(make_judge (mkFix fix) larjv.(i), cst)
	  
    | IsCoFix (i,(lar,lfi,vdef)) ->
        let (larjv,vdefv,cst) = execute_fix mf env lar lfi vdef in
	let larv = Array.map body_of_type larjv in
        let cofix = (i,(larv,lfi,vdefv)) in
        check_cofix env Evd.empty cofix;
	(make_judge (mkCoFix cofix) larjv.(i), cst)
	  
    | IsSort (Prop c) -> 
	(judge_of_prop_contents c, cst0)

    | IsSort (Type u) ->
	judge_of_type u
	  
    | IsAppL (f,args) ->
	let (j,cst1) = execute mf env f in
        let (jl,cst2) = execute_list mf env args in
	let (j,cst3) = apply_rel_list env Evd.empty mf.nocheck jl j in
	let cst = Constraint.union cst1 (Constraint.union cst2 cst3) in
	(j, cst)
	    
    | IsLambda (name,c1,c2) -> 
        let (j,cst1) = execute mf env c1 in
        let var = assumption_of_judgment env Evd.empty j in
	let env1 = push_rel_decl (name,var) env in
        let (j',cst2) = execute mf env1 c2 in 
        let (j,cst3) = abs_rel env1 Evd.empty name var j' in
	let cst = Constraint.union cst1 (Constraint.union cst2 cst3) in
	(j, cst)
	  
     | IsProd (name,c1,c2) ->
        let (j,cst1) = execute mf env c1 in
        let varj = type_judgment env Evd.empty j in
	let env1 = push_rel_decl (name,assumption_of_type_judgment varj) env in
        let (j',cst2) = execute mf env1 c2 in
	let (j,cst3) = gen_rel env1 Evd.empty name varj j' in
	let cst = Constraint.union cst1 (Constraint.union cst2 cst3) in
	(j, cst)

     | IsLetIn (name,c1,c2,c3) ->
        let (j1,cst1) = execute mf env c1 in
        let (j2,cst2) = execute mf env c2 in
	let { uj_val = b; uj_type = t } = cast_rel env Evd.empty j1 j2 in
        let (j3,cst3) = execute mf (push_rel_def (name,b,t) env) c3 in
	let cst = Constraint.union cst1 (Constraint.union cst2 cst3) in
	({ uj_val = mkLetIn (name, j1.uj_val, j2.uj_val, j3.uj_val) ;
	   uj_type = typed_app (subst1 j1.uj_val) j3.uj_type },
	 cst)
	  
    | IsCast (c,t) ->
        let (cj,cst1) = execute mf env c in
        let (tj,cst2) = execute mf env t in
	let cst = Constraint.union cst1 cst2 in
        (cast_rel env Evd.empty cj tj, cst)
	  
    | IsXtra _ -> anomaly "Safe_typing: found an Extra"
	  
and execute_fix mf env lar lfi vdef =
  let (larj,cst1) = execute_array mf env lar in
  let lara = Array.map (assumption_of_judgment env Evd.empty) larj in
  let nlara = 
    List.combine (List.rev lfi) (Array.to_list (vect_lift_type lara)) in
  let env1 = 
    List.fold_left (fun env nvar -> push_rel_decl nvar env) env nlara in
  let (vdefj,cst2) = execute_array mf env1 vdef in
  let vdefv = Array.map j_val_only vdefj in
  let cst3 = type_fixpoint env1 Evd.empty lfi lara vdefj in
  let cst = Constraint.union cst1 (Constraint.union cst2 cst3) in
  (lara,vdefv,cst)

and execute_array mf env v =
  let (jl,u1) = execute_list mf env (Array.to_list v) in
  (Array.of_list jl, u1)

and execute_list mf env = function
  | [] -> 
      ([], Constraint.empty)
  | c::r -> 
      let (j,cst1) = execute mf env c in 
      let (jr,cst2) = execute_list mf env r in
      (j::jr, Constraint.union cst1 cst2)

(* The typed type of a judgment. *)

let execute_type mf env constr = 
  let (j,cst) = execute mf env constr in
  (type_judgment env Evd.empty j, cst)


(* Exported machines.  First safe machines, with no general fixpoint
   allowed (the flag [fix] is not set) and all verifications done (the
   flag [nocheck] is not set). *)

let safe_infer env constr = 
  let mf = { fix = false; nocheck = false } in
  execute mf env constr

let safe_infer_type env constr = 
  let mf = { fix = false; nocheck = false } in
  execute_type mf env constr

(* Machines with general fixpoint. *)

let fix_machine env constr = 
  let mf = { fix = true; nocheck = false } in
  execute mf env constr

let fix_machine_type env constr = 
  let mf = { fix = true; nocheck = false } in
  execute_type mf env constr

(* Fast machines without any verification. *)

let unsafe_infer env constr = 
  let mf = { fix = true; nocheck = true } in
  execute mf env constr

let unsafe_infer_type env constr = 
  let mf = { fix = true; nocheck = true } in
  execute_type mf env constr


(* ``Type of'' machines. *)

let type_of env c = 
  let (j,_) = safe_infer env c in nf_betaiota env Evd.empty (body_of_type j.uj_type)

(* obsolètes
let type_of_type env c = 
  let tt = safe_infer_type env c in DOP0 (Sort (level_of_type tt.typ)

let unsafe_type_of env c = 
  let (j,_) = unsafe_infer env c in nf_betaiota env Evd.empty j.uj_type

let unsafe_type_of_type env c = 
  let tt = unsafe_infer_type env c in DOP0 (Sort tt.typ)
*)
(* Typing of several terms. *)

let safe_infer_l env cl =
  let type_one (cst,l) c =
    let (j,cst') = safe_infer env c in
    (Constraint.union cst cst', j::l)
  in
  List.fold_left type_one (Constraint.empty,[]) cl

let safe_infer_v env cv =
  let type_one (cst,l) c =
    let (j,cst') = safe_infer env c in
    (Constraint.union cst cst', j::l)
  in
  let cst',l = Array.fold_left type_one (Constraint.empty,[]) cv in
  (cst', Array.of_list l)
 

(*s Safe environments. *)

type safe_environment = env

let empty_environment = empty_env

let universes = universes
let context = context
let var_context = var_context

let lookup_var_type = lookup_var_type
let lookup_rel_type = lookup_rel_type
let lookup_var = lookup_var
let lookup_constant = lookup_constant
let lookup_mind = lookup_mind
let lookup_mind_specif = lookup_mind_specif

(* Insertion of variables (named and de Bruijn'ed). They are now typed before
   being added to the environment. *)

let push_rel_or_var_def push (id,c) env =
  let (j,cst) = safe_infer env c in
  let env' = add_constraints cst env in
  push (id,j.uj_val,j.uj_type) env'

let push_var_def nvar env = push_rel_or_var_def push_var_def nvar env

let push_rel_def nrel env = push_rel_or_var_def push_rel_def nrel env

let push_rel_or_var_decl push (id,c) env =
  let (j,cst) = safe_infer_type env c in
  let env' = add_constraints cst env in
  let var = assumption_of_type_judgment j in
  push (id,var) env'

let push_var_decl nvar env = push_rel_or_var_decl push_var_decl nvar env

let push_rel_decl nrel env = push_rel_or_var_decl push_rel_decl nrel env

let push_rels_with_univ vars env =
  List.fold_left (fun env nvar -> push_rel_decl nvar env) env vars

(* Insertion of constants and parameters in environment. *)

let add_constant_with_value sp body typ env =
  let (jb,cst) = safe_infer env body in
  let env' = add_constraints cst env in
  let (env'',ty,cst') = 
    match typ with
      | None -> 
	  env', typed_type_of_judgment env' Evd.empty jb, Constraint.empty
      | Some ty -> 
	  let (jt,cst') = safe_infer env ty in
	  let env'' = add_constraints cst' env' in
	  try
	    let cst'' = conv env'' Evd.empty (body_of_type jb.uj_type) jt.uj_val in
	    let env'' = add_constraints cst'' env'' in
	    (env'', assumption_of_judgment env'' Evd.empty jt, 
	     Constraint.union cst' cst'')
	  with NotConvertible -> 
	    error_actual_type CCI env jb.uj_val (body_of_type jb.uj_type) jt.uj_val
  in
  let ids = 
    Idset.union (global_vars_set body) (global_vars_set (body_of_type ty))
  in
  let cb = { 
    const_kind = kind_of_path sp;
    const_body = Some (ref (Cooked body));
    const_type = ty;
    const_hyps = keep_hyps ids (var_context env);
    const_constraints = Constraint.union cst cst';
    const_opaque = false } 
  in
  add_constant sp cb env''

let add_lazy_constant sp f t env =
  let (jt,cst) = safe_infer env t in
  let env' = add_constraints cst env in
  let ids = global_vars_set jt.uj_val in
  let cb = {
    const_kind = kind_of_path sp;
    const_body = Some (ref (Recipe f));
    const_type = assumption_of_judgment env' Evd.empty jt;
    const_hyps = keep_hyps ids (var_context env);
    const_constraints = cst;
    const_opaque = false } 
  in
  add_constant sp cb env'

let add_constant sp ce env =
  match ce.const_entry_body with
    | Cooked c -> add_constant_with_value sp c ce.const_entry_type env
    | Recipe f -> 
	(match ce.const_entry_type with
	   | Some typ -> add_lazy_constant sp f typ env
	   | None -> error "you cannot declare a lazy constant without type")

let add_parameter sp t env =
  let (jt,cst) = safe_infer env t in
  let env' = add_constraints cst env in
  let ids = global_vars_set jt.uj_val in
  let cb = {
    const_kind = kind_of_path sp;
    const_body = None;
    const_type = assumption_of_judgment env' Evd.empty jt;
    const_hyps = keep_hyps ids (var_context env);
    const_constraints = cst;
    const_opaque = false } 
  in
  Environ.add_constant sp cb env'

(* Insertion of inductive types. *)

(* Only the case where at least s1 or s2 is a [Type] is taken into account *)
let max_universe (s1,cst1) (s2,cst2) g =
  match s1,s2 with
    | Type u1, Type u2 ->
	let (u12,cst) = sup u1 u2 g in
	Type u12, Constraint.union cst (Constraint.union cst1 cst2)
    | Type u1, _  -> s1, cst1
    | _, _ -> s2, cst2

(* This (re)computes informations relevant to extraction and the sort of an
   arity or type constructor; we do not to recompute universes constraints *)

let rec infos_and_sort env t =
  match kind_of_term t with
    | IsProd (name,c1,c2) ->
        let (varj,_) = safe_infer_type env c1 in
	let var = assumption_of_type_judgment varj in
	let env1 = Environ.push_rel_decl (name,var) env in
	let s1 = varj.utj_type in
	let logic = not (is_info_type env Evd.empty varj) in
	let small = is_small s1 in
	(logic,small) :: (infos_and_sort env1 c2)
    | IsCast (c,_) -> infos_and_sort env c
    | _ -> []

(* [infos] is a sequence of pair [islogic,issmall] for each type in
   the product of a constructor or arity *)

let is_small infos = List.for_all (fun (logic,small) -> small) infos
let is_logic_constr infos = List.for_all (fun (logic,small) -> logic) infos
let is_logic_arity infos =
  List.for_all (fun (logic,small) -> logic || small) infos

let is_unit arinfos constrsinfos =
  match constrsinfos with  (* One info = One constructor *)
   | [constrinfos] -> is_logic_constr constrinfos && is_logic_arity arinfos
   | _ -> false

let small_unit constrsinfos (env_ar,nparams,ar) =
  let issmall = List.for_all is_small constrsinfos in
  let arinfos =
    let (params,a) = mind_extract_params nparams ar in
    let env_par = push_rels params env_ar in
    infos_and_sort env_par a in
  let isunit = is_unit arinfos constrsinfos in
  issmall, isunit

(* [smax] is the max of the sorts of the products of the constructor type *)

let enforce_type_constructor arsort smax cst =
  match smax, arsort with
    | Type uc, Type ua -> Constraint.add (ua,Geq,uc) cst
    | _,_ -> cst

let type_one_constructor env_ar nparams arsort c =
  let infos = 
    let (params,dc) = mind_extract_params nparams c in
    let env_par = push_rels params env_ar in
    infos_and_sort env_par dc in
  (* Constructors are typed-checked here *)
  let (j,cst) = safe_infer_type env_ar c in

  (* If the arity is at some level Type arsort, then the sort of the
     constructor must be below arsort; here we consider constructors with the
     global parameters (which add a priori more constraints on their sort) *)
  let cst2 = enforce_type_constructor arsort j.utj_type cst in

  (infos, assumption_of_type_judgment j, cst2)

let type_one_inductive i env_ar env_par nparams ninds (id,ar,cnames,vc) =
  let arsort = sort_of_arity env_ar ar in
  let (constrsinfos,jlc,cst) = 
    List.fold_right
      (fun c (infosl,jl,cst) -> 
	 let (infos,jc,cst') = type_one_constructor env_ar nparams arsort c in
	 (infos::infosl,jc::jl, Constraint.union cst cst'))
      vc
      ([],[],Constraint.empty)
  in
  let vc' = Array.of_list jlc in
  let issmall,isunit = small_unit constrsinfos (env_par,nparams,ar) in
  let (_,tyar) = lookup_rel_type (ninds+1-i) env_ar in
  ((id,tyar,cnames,issmall,isunit,vc'), cst)

let add_mind sp mie env =
  mind_check_names mie;
  mind_check_arities env mie;
  let params = mind_extract_and_check_params mie in
  let nparams = mie.mind_entry_nparams in
  mind_check_lc params mie;
  let ninds = List.length mie.mind_entry_inds in
  let types_sign = 
    List.map (fun (id,ar,_,_) -> (Name id,ar)) mie.mind_entry_inds
  in
  (* Arities with params are typed-checked here *)
  let env_arities = push_rels_with_univ types_sign env in
  let env_params = push_rels params env_arities in
  let _,inds,cst =
    List.fold_right
      (fun ind (i,inds,cst) -> 
	 let (ind',cst') = 
	   type_one_inductive i env_arities env_params nparams ninds ind 
	 in
	 (succ i,ind'::inds, Constraint.union cst cst'))
      mie.mind_entry_inds
      (1,[],Constraint.empty) 
  in
  let kind = kind_of_path sp in
  let mib = 
    cci_inductive env env_arities kind nparams mie.mind_entry_finite inds cst
  in
  add_mind sp mib (add_constraints cst env)
    
let add_constraints = add_constraints

let rec pop_vars idl env =
  match idl with 
    | [] -> env
    | id::l -> pop_vars l (Environ.pop_var id env)

let export = export
let import = import

let env_of_safe_env e = e

