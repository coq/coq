
(* $Id$ *)

open Pp
open Util
open Names
open Univ
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
let vect_lift_type = Array.mapi (fun i t -> type_app (lift i) t)

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
	(make_judge cstr (lookup_named_type id env), cst0)

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
	let inst_u = if u == dummy_univ then new_univ() else u in
	judge_of_type inst_u
	  
    | IsApp (f,args) ->
	let (j,cst1) = execute mf env f in
        let (jl,cst2) = execute_array mf env args in
	let (j,cst3) =
	  apply_rel_list env Evd.empty mf.nocheck (Array.to_list jl) j in
	let cst = Constraint.union cst1 (Constraint.union cst2 cst3) in
	(j, cst)
	    
    | IsLambda (name,c1,c2) -> 
        let (j,cst1) = execute mf env c1 in
        let var = assumption_of_judgment env Evd.empty j in
	let env1 = push_rel_assum (name,var) env in
        let (j',cst2) = execute mf env1 c2 in 
        let (j,cst3) = abs_rel env1 Evd.empty name var j' in
	let cst = Constraint.union cst1 (Constraint.union cst2 cst3) in
	(j, cst)
	  
     | IsProd (name,c1,c2) ->
        let (j,cst1) = execute mf env c1 in
        let varj = type_judgment env Evd.empty j in
	let env1 = push_rel_assum (name,varj.utj_val) env in
        let (j',cst2) = execute mf env1 c2 in
        let varj' = type_judgment env Evd.empty j' in
	let (j,cst3) = gen_rel env1 Evd.empty name varj varj' in
	let cst = Constraint.union cst1 (Constraint.union cst2 cst3) in
	(j, cst)

     | IsLetIn (name,c1,c2,c3) ->
        let (j1,cst1) = execute mf env c1 in
        let (j2,cst2) = execute mf env c2 in
	let tj2 = assumption_of_judgment env Evd.empty j2 in
	let ({uj_val = b; uj_type = t},cst0) = cast_rel env Evd.empty j1 tj2 in
        let (j3,cst3) = execute mf (push_rel_def (name,b,t) env) c3 in
	let cst = Constraint.union cst1 (Constraint.union cst2 cst3) in
	({ uj_val = mkLetIn (name, j1.uj_val, tj2, j3.uj_val) ;
	   uj_type = type_app (subst1 j1.uj_val) j3.uj_type },
	 Constraint.union cst cst0)
	  
    | IsCast (c,t) ->
        let (cj,cst1) = execute mf env c in
        let (tj,cst2) = execute mf env t in
	let tj = assumption_of_judgment env Evd.empty tj in
	let cst = Constraint.union cst1 cst2 in
	let (j, cst0) = cast_rel env Evd.empty cj tj in
	(j, Constraint.union cst cst0)
	  
    | IsXtra _ -> anomaly "Safe_typing: found an Extra"
	  
and execute_fix mf env lar lfi vdef =
  let (larj,cst1) = execute_array mf env lar in
  let lara = Array.map (assumption_of_judgment env Evd.empty) larj in
  let nlara = 
    List.combine (List.rev lfi) (Array.to_list (vect_lift_type lara)) in
  let env1 = 
    List.fold_left (fun env nvar -> push_rel_assum nvar env) env nlara in
  let (vdefj,cst2) = execute_array mf env1 vdef in
  let vdefv = Array.map j_val vdefj in
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
  let (j,_) = safe_infer env c in
  nf_betaiota env Evd.empty (body_of_type j.uj_type)

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
let named_context = named_context

let lookup_named_type = lookup_named_type
let lookup_rel_type = lookup_rel_type
let lookup_named = lookup_named
let lookup_constant = lookup_constant
let lookup_mind = lookup_mind
let lookup_mind_specif = lookup_mind_specif

(* Insertion of variables (named and de Bruijn'ed). They are now typed before
   being added to the environment. *)

let push_rel_or_named_def push (id,b) env =
  let (j,cst) = safe_infer env b in
  let env' = add_constraints cst env in
  push (id,j.uj_val,j.uj_type) env'

let push_named_def = push_rel_or_named_def push_named_def
let push_rel_def = push_rel_or_named_def push_rel_def

let push_rel_or_named_assum push (id,t) env =
  let (j,cst) = safe_infer env t in
  let env' = add_constraints cst env in
  let t = assumption_of_judgment env Evd.empty j in
  push (id,t) env'

let push_named_assum = push_rel_or_named_assum push_named_assum
let push_rel_assum = push_rel_or_named_assum push_rel_assum

let push_rels_with_univ vars env =
  List.fold_left (fun env nvar -> push_rel_assum nvar env) env vars

(* Insertion of constants and parameters in environment. *)

let add_parameter sp t env =
  let (jt,cst) = safe_infer env t in
  let env' = add_constraints cst env in
  let ids = global_vars_set jt.uj_val in
  let cb = {
    const_kind = kind_of_path sp;
    const_body = None;
    const_type = assumption_of_judgment env' Evd.empty jt;
    const_hyps = keep_hyps ids (named_context env);
    const_constraints = cst;
    const_opaque = false } 
  in
  Environ.add_constant sp cb env'

let add_constant_with_value sp body typ env =
  let body' =
    match typ with
      | None -> body
      | Some ty -> mkCast (body, ty) in
  let (jb,cst) = safe_infer env body' in
  let env' = add_constraints cst env in
  let ty = jb.uj_type in
  let ids = 
    Idset.union (global_vars_set body) (global_vars_set (body_of_type ty))
  in
  let cb = { 
    const_kind = kind_of_path sp;
    const_body = Some body;
    const_type = ty;
    const_hyps = keep_hyps ids (named_context env);
    const_constraints = cst;
    const_opaque = false } 
  in
  add_constant sp cb env'

let add_discharged_constant sp r env =
  let (body,typ) = Cooking.cook_constant env r in
  match body with
    | None -> 
	add_parameter sp typ env
    | Some c -> 
	(* let c = hcons1_constr c in *)
	let (jtyp,cst) = safe_infer env typ in
	let env' = add_constraints cst env in
	let ids = 
	  Idset.union (global_vars_set c) 
	    (global_vars_set (body_of_type jtyp.uj_val))
	in
	let cb = { const_kind = kind_of_path sp;
		   const_body = Some c;
		   const_type = assumption_of_judgment env' Evd.empty jtyp;
		   const_hyps = keep_hyps ids (named_context env);
		   const_constraints = cst;
		   const_opaque = false } 
	in
	add_constant sp cb env'

let add_constant sp ce env =
  add_constant_with_value sp ce.const_entry_body ce.const_entry_type env

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
	let env1 = Environ.push_rel_assum (name,varj.utj_val) env in
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
    infos_and_sort env_par dc 
  in
  (* Constructors are typed-checked here *)
  let (j,cst) = safe_infer_type env_ar c in

  (* If the arity is at some level Type arsort, then the sort of the
     constructor must be below arsort; here we consider constructors with the
     global parameters (which add a priori more constraints on their sort) *)
  let cst2 = enforce_type_constructor arsort j.utj_type cst in

  (infos, j.utj_val, cst2)

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
	 (i-1,ind'::inds, Constraint.union cst cst'))
      mie.mind_entry_inds
      (ninds,[],Constraint.empty) 
  in
  let kind = kind_of_path sp in
  let mib = 
    cci_inductive env env_arities kind nparams mie.mind_entry_finite inds cst
  in
  add_mind sp mib (add_constraints cst env)
    
let add_constraints = add_constraints

let rec pop_named_decls idl env =
  match idl with 
    | [] -> env
    | id::l -> pop_named_decls l (Environ.pop_named_decl id env)

let set_opaque = Environ.set_opaque
let set_transparent = Environ.set_transparent

let export = export
let import = import

let env_of_safe_env e = e

