
(* $Id$ *)

open Pp
open Util
open Names
open Univ
open Generic
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
let j_type j = j.uj_type
let j_kind j = j.uj_kind

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
	(relative env n, cst0)

    | IsVar id -> 
	(make_judge cstr (snd (lookup_var id env)), cst0)

    | IsAbst _ ->
        if evaluable_abst env cstr then 
	  execute mf env (abst_value env cstr)
        else 
	  error "Cannot typecheck an unevaluable abstraction"

    (* ATTENTION : faudra faire le typage du contexte des Const,
    MutInd et MutConstructsi un jour cela devient des constructions
    arbitraires et non plus des variables *)

    | IsConst c ->
        (make_judge cstr (type_of_constant env Evd.empty c), cst0)
	  
    | IsMutInd ind ->
	(make_judge cstr (type_of_inductive env Evd.empty ind), cst0)
	  
    | IsMutConstruct c -> 
	let (typ,kind) =destCast (type_of_constructor env Evd.empty c) in
        ({ uj_val = cstr; uj_type = typ; uj_kind = kind } , cst0)
	  
    | IsMutCase (ci,p,c,lf) ->
        let (cj,cst1) = execute mf env c in
        let (pj,cst2) = execute mf env p in
        let (lfj,cst3) = execute_array mf env lf in
	let cst = Constraint.union cst1 (Constraint.union cst2 cst3) in
        (type_of_case env Evd.empty ci pj cj lfj, cst)
  
    | IsFix (vn,i,lar,lfi,vdef) ->
        if (not mf.fix) && array_exists (fun n -> n < 0) vn then
          error "General Fixpoints not allowed";
        let (larv,vdefv,cst) = execute_fix mf env lar lfi vdef in
        let fix = mkFix vn i larv lfi vdefv in
        check_fix env Evd.empty fix;
	(make_judge fix larv.(i), cst)
	  
    | IsCoFix (i,lar,lfi,vdef) ->
        let (larv,vdefv,cst) = execute_fix mf env lar lfi vdef in
        let cofix = mkCoFix i larv lfi vdefv in
        check_cofix env Evd.empty cofix;
	(make_judge cofix larv.(i), cst)
	  
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
	let env1 = push_rel (name,var) env in
        let (j',cst2) = execute mf env1 c2 in 
        let (j,cst3) = abs_rel env1 Evd.empty name var j' in
	let cst = Constraint.union cst1 (Constraint.union cst2 cst3) in
	(j, cst)
	  
     | IsProd (name,c1,c2) ->
        let (j,cst1) = execute mf env c1 in
        let var = assumption_of_judgment env Evd.empty j in
	let env1 = push_rel (name,var) env in
        let (j',cst2) = execute mf env1 c2 in
	let (j,cst3) = gen_rel env1 Evd.empty name var j' in
	let cst = Constraint.union cst1 (Constraint.union cst2 cst3) in
	(j, cst)
	  
    | IsCast (c,t) ->
        let (cj,cst1) = execute mf env c in
        let (tj,cst2) = execute mf env t in
	let cst = Constraint.union cst1 cst2 in
        (cast_rel env Evd.empty cj tj, cst)
	  
      | _ -> error_cant_execute CCI env cstr
	  
and execute_fix mf env lar lfi vdef =
  let (larj,cst1) = execute_array mf env lar in
  let lara = Array.map (assumption_of_judgment env Evd.empty) larj in
  let nlara = 
    List.combine (List.rev lfi) (Array.to_list (vect_lift_type lara)) in
  let env1 = 
    List.fold_left (fun env nvar -> push_rel nvar env) env nlara in
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
  (assumption_of_judgment env Evd.empty j, cst)


(* Exported machines.  First safe machines, with no general fixpoint
   allowed (the flag [fix] is not set) and all verifications done (the
   flag [nocheck] is not set). *)

let safe_machine env constr = 
  let mf = { fix = false; nocheck = false } in
  execute mf env constr

let safe_machine_type env constr = 
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

let unsafe_machine env constr = 
  let mf = { fix = true; nocheck = true } in
  execute mf env constr

let unsafe_machine_type env constr = 
  let mf = { fix = true; nocheck = true } in
  execute_type mf env constr


(* ``Type of'' machines. *)

let type_of env c = 
  let (j,_) = safe_machine env c in nf_betaiota env Evd.empty j.uj_type

(* obsolètes
let type_of_type env c = 
  let tt = safe_machine_type env c in DOP0 (Sort (level_of_type tt.typ)

let unsafe_type_of env c = 
  let (j,_) = unsafe_machine env c in nf_betaiota env Evd.empty j.uj_type

let unsafe_type_of_type env c = 
  let tt = unsafe_machine_type env c in DOP0 (Sort tt.typ)
*)
(* Typing of several terms. *)

let safe_machine_l env cl =
  let type_one (cst,l) c =
    let (j,cst') = safe_machine env c in
    (Constraint.union cst cst', j::l)
  in
  List.fold_left type_one (Constraint.empty,[]) cl

let safe_machine_v env cv =
  let type_one (cst,l) c =
    let (j,cst') = safe_machine env c in
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

let lookup_var = lookup_var
let lookup_rel = lookup_rel
let lookup_constant = lookup_constant
let lookup_mind = lookup_mind
let lookup_mind_specif = lookup_mind_specif

(* Insertion of variables (named and de Bruijn'ed). They are now typed before
   being added to the environment. *)

let push_rel_or_var push (id,c) env =
  let (j,cst) = safe_machine env c in
  let env' = add_constraints cst env in
  let var = assumption_of_judgment env' Evd.empty j in
  push (id,var) env'

let push_var nvar env = push_rel_or_var push_var nvar env

let push_rel nrel env = push_rel_or_var push_rel nrel env

let push_vars vars env =
  List.fold_left (fun env nvar -> push_var nvar env) env vars

let push_rels vars env =
  List.fold_left (fun env nvar -> push_rel nvar env) env vars

(* Insertion of constants and parameters in environment. *)

let add_constant_with_value sp body typ env =
  let (jb,cst) = safe_machine env body in
  let env' = add_constraints cst env in
  let (env'',ty,cst') = 
    match typ with
      | None -> 
	  env', typed_type_of_judgment env' Evd.empty jb, Constraint.empty
      | Some ty -> 
	  let (jt,cst') = safe_machine env ty in
	  let env'' = add_constraints cst' env' in
	  try
	    let cst'' = conv env'' Evd.empty jb.uj_type jt.uj_val in
	    let env'' = add_constraints cst'' env'' in
	    (env'', assumption_of_judgment env'' Evd.empty jt, 
	     Constraint.union cst' cst'')
	  with NotConvertible -> 
	    error_actual_type CCI env jb.uj_val jb.uj_type jt.uj_val
  in
  let ids = 
    Idset.union (global_vars_set body) (global_vars_set (body_of_type ty))
  in
  let cb = { 
    const_kind = kind_of_path sp;
    const_body = Some (ref (Cooked body));
    const_type = ty;
    const_hyps = keep_hyps (var_context env) ids;
    const_constraints = Constraint.union cst cst';
    const_opaque = false } 
  in
  add_constant sp cb env''

let add_lazy_constant sp f t env =
  let (jt,cst) = safe_machine env t in
  let env' = add_constraints cst env in
  let ids = global_vars_set jt.uj_val in
  let cb = {
    const_kind = kind_of_path sp;
    const_body = Some (ref (Recipe f));
    const_type = assumption_of_judgment env' Evd.empty jt;
    const_hyps = keep_hyps (var_context env) ids;
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
  let (jt,cst) = safe_machine env t in
  let env' = add_constraints cst env in
  let ids = global_vars_set jt.uj_val in
  let cb = {
    const_kind = kind_of_path sp;
    const_body = None;
    const_type = assumption_of_judgment env' Evd.empty jt;
    const_hyps = keep_hyps (var_context env) ids;
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

(* This (re)computes informations relevant to extraction and the sort of
   an arity or type constructor *)

let rec infos_and_sort env t =
  match kind_of_term t with
    | IsProd (name,c1,c2) ->
        let (var,cst1) = safe_machine_type env c1 in
	let env1 = Environ.push_rel (name,var) env in
	let (infos,smax,cst) = infos_and_sort env1 c2 in
	let s1 = level_of_type var in
	let smax',cst' = max_universe (s1,cst1) (smax,cst) (universes env) in
	let logic = not (is_info_type env Evd.empty var) in
	let small = is_small s1 in
	((logic,small) :: infos, smax', cst')
    | IsCast (c,t) -> infos_and_sort env c
    | _ ->
	([],prop (* = neutral element of max_universe *),Constraint.empty)

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

let small_unit constrsinfos (env_par,nparams,ar) =
  let issmall = List.for_all is_small constrsinfos in
  let (arinfos,_,_) =
    let (_,a) = mind_extract_params nparams ar in infos_and_sort env_par a in
  let isunit = is_unit arinfos constrsinfos in
  issmall, isunit

(* [smax] is the max of the sorts of the products of the constructor type *)

let enforce_type_constructor arsort smax cst =
  match smax, arsort with
    | Type uc, Type ua -> Constraint.add (ua,Geq,uc) cst
    | _,_ -> cst

let type_one_constructor env_ar nparams arsort c =
  let (infos,max,cst1) = 
    let (params,dc) = mind_extract_params nparams c in
    let env_par = push_rels params env_ar in
    infos_and_sort env_par dc in
  let (j,cst2) = safe_machine_type env_ar c in
  (*C'est idiot, cst1 et cst2 sont essentiellement des copies l'un de l'autre*)
  let cst3 =enforce_type_constructor arsort max (Constraint.union cst1 cst2) in
  (infos, j, cst3)

let type_one_inductive i env_ar env_par nparams ninds (id,ar,cnames,spec) =
  let (lna,vc) = decomp_all_DLAMV_name spec in
  let arsort = sort_of_arity env_ar ar in
  let (constrsinfos,jlc,cst') = 
    List.fold_right
      (fun c (infosl,jl,cst) -> 
	 let (infos,jc,cst') = type_one_constructor env_ar nparams arsort c in
	 (infos::infosl,jc::jl, Constraint.union cst cst'))
      (Array.to_list vc) 
      ([],[],Constraint.empty)
  in
  let castlc = List.map incast_type jlc in
  let spec' = put_DLAMSV lna (Array.of_list castlc) in
  let issmall,isunit = small_unit constrsinfos (env_par,nparams,ar) in
  let (_,tyar) = lookup_rel (ninds+1-i) env_ar in
  ((id,tyar,cnames,issmall,isunit,spec'), cst')

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
  let env_arities = push_rels types_sign env in
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

let pop_vars idl env =
  let rec remove n sign = 
    if n = 0 then
      sign
    else
      if isnull_sign sign then anomaly "pop_vars"
      else
	let (id,_) = hd_sign sign in 
	    if not (List.mem id idl) then anomaly "pop_vars";
	    remove (pred n) (tl_sign sign)
  in
  change_hyps (remove (List.length idl)) env

let export = export
let import = import

let env_of_safe_env e = e

(*s Machines with information. *)

type information = Logic | Inf of unsafe_judgment
