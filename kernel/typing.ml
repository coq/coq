
(* $Id$ *)

open Pp
open Util
open Names
open Univ
open Generic
open Term
open Reduction
open Sign
open Constant
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
  let u0 = universes env in
  match kind_of_term cstr with
    | IsMeta n ->
       	let metaty =
          try lookup_meta n env
          with Not_found -> error "A variable remains non instanciated" 
	in
        (match kind_of_term metaty with
           | IsCast (typ,kind) -> 
	       ({ uj_val = cstr; uj_type = typ; uj_kind = kind }, u0)
           | _ ->
	       let (jty,u1) = execute mf env metaty in
	       let k = whd_betadeltaiotaeta env jty.uj_type in
	       ({ uj_val = cstr; uj_type = metaty; uj_kind = k }, u1))
	
    | IsRel n -> 
	(relative env n, u0)

    | IsVar id -> 
	(make_judge cstr (snd (lookup_var id env)), u0)
	  
    | IsAbst _ ->
        if evaluable_abst env cstr then 
	  execute mf env (abst_value env cstr)
        else 
	  error "Cannot typecheck an unevaluable abstraction"
	      
    | IsConst _ ->
        (make_judge cstr (type_of_constant_or_existential env cstr), u0)
	  
    | IsMutInd _ ->
	(make_judge cstr (type_of_inductive env cstr), u0)
	  
    | IsMutConstruct _ -> 
	let (typ,kind) = destCast (type_of_constructor env cstr) in
        ({ uj_val = cstr; uj_type = typ; uj_kind = kind } , u0)
	  
    | IsMutCase (_,p,c,lf) ->
        let (cj,u1) = execute mf env c in
	let env1 = set_universes u1 env in
        let (pj,u2) = execute mf env1 p in
	let env2 = set_universes u2 env1 in
        let (lfj,u3) = execute_array mf env2 lf in
	let env3 = set_universes u3 env2 in
        (type_of_case env3 pj cj lfj, u3)
  
    | IsFix (vn,i,lar,lfi,vdef) ->
        if (not mf.fix) && array_exists (fun n -> n < 0) vn then
          error "General Fixpoints not allowed";
        let (larv,vdefv,u1) = execute_fix mf env lar lfi vdef in
        let fix = mkFix vn i larv lfi vdefv in
        check_fix env fix;
	(make_judge fix larv.(i), u1)
	  
    | IsCoFix (i,lar,lfi,vdef) ->
        let (larv,vdefv,u1) = execute_fix mf env lar lfi vdef in
        let cofix = mkCoFix i larv lfi vdefv in
        check_cofix env cofix;
	(make_judge cofix larv.(i), u1)
	  
    | IsSort (Prop c) -> 
	(type_of_prop_or_set c, u0)

    | IsSort (Type u) ->
	type_of_type u u0
	  
    | IsAppL a ->
	let la = Array.length a in
	if la = 0 then error_cant_execute CCI env cstr;
	let hd = a.(0)
	and tl = Array.to_list (Array.sub a 1 (la - 1)) in
	let (j,u1) = execute mf env hd in
	let env1 = set_universes u1 env in
        let (jl,u2) = execute_list mf env1 tl in
	let env2 = set_universes u2 env1 in
	apply_rel_list env2 mf.nocheck jl j
	    
    | IsLambda (name,c1,c2) -> 
        let (j,u1) = execute mf env c1 in
        let var = assumption_of_judgment env j in
	let env1 = push_rel (name,var) (set_universes u1 env) in
        let (j',u2) = execute mf env1 c2 in 
	let env2 = set_universes u2 env1 in
        abs_rel env2 name var j'
	  
    | IsProd (name,c1,c2) ->
        let (j,u1) = execute mf env c1 in
        let var = assumption_of_judgment env j in
	let env1 = push_rel (name,var) (set_universes u1 env) in
        let (j',u2) = execute mf env1 c2 in
	let env2 = set_universes u2 env1 in
        gen_rel env2 name var j'
	  
    | IsCast (c,t) ->
        let (cj,u1) = execute mf env c in
	let env1 = set_universes u1 env in
        let (tj,u2) = execute mf env1 t in
	let env2 = set_universes u2 env1 in
        (cast_rel env2 cj tj, u2)
	  
      | _ -> error_cant_execute CCI env cstr
	  
and execute_fix mf env lar lfi vdef =
  let (larj,u1) = execute_array mf env lar in
  let env1 = set_universes u1 env in
  let lara = Array.map (assumption_of_judgment env1) larj in
  let nlara = 
    List.combine (List.rev lfi) (Array.to_list (vect_lift_type lara)) in
  let env2 = 
    List.fold_left (fun env nvar -> push_rel nvar env) env1 nlara in
  let (vdefj,u2) = execute_array mf env2 vdef in
  let env3 = set_universes u2 env2 in
  let vdefv = Array.map j_val_only vdefj in
  let u3 = type_fixpoint env3 lfi lara vdefj in
  (lara,vdefv,u3)

and execute_array mf env v =
  let (jl,u1) = execute_list mf env (Array.to_list v) in
  (Array.of_list jl, u1)

and execute_list mf env = function
  | [] -> ([], universes env)
  | c::r -> 
      let (j,u') = execute mf env c in 
      let (jr,u'') = execute_list mf (set_universes u' env) r in
      (j::jr, u'')


(* The typed type of a judgment. *)

let execute_type mf env constr = 
  let (j,_) = execute mf env constr in
  assumption_of_judgment env j


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
  let (j,_) = safe_machine env c in nf_betaiota env j.uj_type

let type_of_type env c = 
  let tt = safe_machine_type env c in DOP0 (Sort tt.typ)

let unsafe_type_of env c = 
  let (j,_) = unsafe_machine env c in nf_betaiota env j.uj_type

let unsafe_type_of_type env c = 
  let tt = unsafe_machine_type env c in DOP0 (Sort tt.typ)

(* Typing of several terms. *)

let safe_machine_l env cl =
  let type_one (env,l) c =
    let (j,u) = safe_machine env c in
    (set_universes u env, j::l)
  in
  List.fold_left type_one (env,[]) cl

let safe_machine_v env cv =
  let type_one (env,l) c =
    let (j,u) = safe_machine env c in
    (set_universes u env, j::l)
  in
  let env',l = Array.fold_left type_one (env,[]) cv in
  (env', Array.of_list l)
 

(*s Safe environments. *)

type 'a environment = 'a unsafe_env

let empty_environment = empty_env

let evar_map = evar_map
let universes = universes
let metamap = metamap
let context = context

let lookup_var = lookup_var
let lookup_rel = lookup_rel
let lookup_constant = lookup_constant
let lookup_mind = lookup_mind
let lookup_mind_specif = lookup_mind_specif
let lookup_meta = lookup_meta

(* Insertion of variables (named and de Bruijn'ed). They are now typed before
   being added to the environment. *)

let push_rel_or_var push (id,c) env =
  let (j,u) = safe_machine env c in
  let env' = set_universes u env in
  let var = assumption_of_judgment env' j in
  push (id,var) env'

let push_var nvar env = push_rel_or_var push_var nvar env

let push_rel nrel env = push_rel_or_var push_rel nrel env

let push_vars vars env =
  List.fold_left (fun env nvar -> push_var nvar env) env vars

let push_rels vars env =
  List.fold_left (fun env nvar -> push_rel nvar env) env vars

(* Insertion of constants and parameters in environment. *)

let add_constant sp ce env =
  let (jb,u) = safe_machine env ce.const_entry_body in
  let env' = set_universes u env in
  let (env'',ty) = 
    match ce.const_entry_type with
      | None -> 
	  env', typed_type_of_judgment env' jb
      | Some ty -> 
	  let (jt,u') = safe_machine env ty in
	  let env'' = set_universes u' env' in
	  match conv env'' jb.uj_type jt.uj_val with
	    | Convertible u'' -> 
		let env'' = set_universes u'' env' in
		env'', assumption_of_judgment env'' jt
	    | NotConvertible -> 
		error_actual_type CCI env jb.uj_val jb.uj_type jt.uj_val
  in
  let cb = { 
    const_kind = kind_of_path sp;
    const_body = Some (ref (Cooked ce.const_entry_body));
    const_type = ty;
    const_hyps = get_globals (context env);
    const_opaque = false } 
  in
  add_constant sp cb env''

let type_from_judgment env j =
  match whd_betadeltaiota env j.uj_kind with
    | DOP0(Sort s) -> { body = j.uj_type; typ = s }
    | _ -> error_not_type CCI env j.uj_type (* shouldn't happen *)

let add_parameter sp c env =
  let (j,u) = safe_machine env c in
  let env' = set_universes u env in
  let cb = {
    const_kind = kind_of_path sp;
    const_body = Some (ref (Cooked c));
    const_type = type_from_judgment env' j;
    const_hyps = get_globals (context env);
    const_opaque = false } 
  in
  Environ.add_constant sp cb env'

(* Insertion of inductive types. *)

(* [for_all_prods p env c] checks a boolean condition [p] on all types
   appearing in products in front of [c]. The boolean condition [p] is a 
   function taking a value of type [typed_type] as argument. *)

let rec for_all_prods p env c =
  match whd_betadeltaiota env c with
    | DOP2(Prod, DOP2(Cast,t,DOP0 (Sort s)), DLAM(name,c)) -> 
	(p (make_typed t s)) &&
	(let ty = { body = t; typ = s } in
	 let env' = Environ.push_rel (name,ty) env in
	 for_all_prods p env' c)
    | DOP2(Prod, b, DLAM(name,c)) -> 
	let (jb,u) = unsafe_machine env b in
	let var = assumption_of_judgment env jb in
	(p var) &&
	(let env' = Environ.push_rel (name,var) (set_universes u env) in
	 for_all_prods p env' c)
    | _ -> true

let is_small_type e c = for_all_prods (fun t -> is_small t.typ) e c

let enforce_type_constructor env univ j =
  match whd_betadeltaiota env j.uj_type with
    | DOP0 (Sort (Type uc)) -> 
	let u = universes env in
	set_universes (enforce_geq univ uc u) env
    | _ -> error "Type of Constructor not well-formed"

let type_one_constructor env_ar nparams ar c =
  let (params,dc) = decompose_prod_n nparams c in
  let env_par = push_rels params env_ar in
  let (jc,u) = safe_machine env_par dc in
  let env_par' = set_universes u env_par in
  let env_par'' = match sort_of_arity env_ar ar with
    | Type u -> enforce_type_constructor env_par' u jc
    | Prop _ -> env_par'
  in
  let env_ar' = set_universes (universes env_par'') env_ar in
  let (j,u) = safe_machine env_ar' c in
  let issmall = is_small_type env_par c in
  (set_universes u env_ar', (issmall,j))

let logic_constr env c =
  for_all_prods (fun t -> not (is_info_type env t)) env c

let logic_arity env c =
  for_all_prods 
    (fun t -> (not (is_info_type env t)) or (is_small_type env t.body)) env c

let is_unit env_par nparams ar spec =
  match decomp_all_DLAMV_name spec with
    | (_,[|c|]) ->
	(let (_,a) = decompose_prod_n nparams ar in logic_arity env_par ar) &&
	(let (_,c') = decompose_prod_n nparams c in logic_constr env_par c')
    | _ -> false

let type_one_inductive i env_ar env_par nparams ninds (id,ar,cnames,spec) =
  let (lna,vc) = decomp_all_DLAMV_name spec in
  let (env',(issmall,jlc)) = 
    List.fold_left 
      (fun (env,(small,jl)) c -> 
	 let (env',(sm,jc)) = type_one_constructor env nparams ar c in
	 (env', (small && sm,jc::jl)))
      (env_ar,(true,[])) (Array.to_list vc)
  in
  let castlc = List.map cast_of_judgment jlc in
  let spec' = put_DLAMSV lna (Array.of_list castlc) in
  let isunit = is_unit env_par nparams ar spec in
  let (_,tyar) = lookup_rel (ninds+1-i) env' in
  (env', (id,tyar,cnames,issmall,isunit,spec'))

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
  let env_arities',_,inds =
    List.fold_left 
      (fun (env,i,inds) ind -> 
	 let (env',ind') = 
	   type_one_inductive i env env_params nparams ninds ind 
	 in
	 (env',succ i,ind'::inds))
      (env_arities,1,[]) mie.mind_entry_inds
  in
  let kind = kind_of_path sp in
  let mib = 
    cci_inductive env env_arities' kind nparams mie.mind_entry_finite inds
  in
  add_mind sp mib (set_universes (universes env_arities') env)


(*s Machines with information. *)

type information = Logic | Inf of unsafe_judgment
