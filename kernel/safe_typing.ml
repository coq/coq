
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
	      
    | IsConst _ ->
        (make_judge cstr (type_of_constant env Evd.empty cstr), cst0)
	  
    | IsMutInd _ ->
	(make_judge cstr (type_of_inductive env Evd.empty cstr), cst0)
	  
    | IsMutConstruct _ -> 
	let (typ,kind) = destCast (type_of_constructor env Evd.empty cstr) in
        ({ uj_val = cstr; uj_type = typ; uj_kind = kind } , cst0)
	  
    | IsMutCase (_,p,c,lf) ->
        let (cj,cst1) = execute mf env c in
        let (pj,cst2) = execute mf env p in
        let (lfj,cst3) = execute_array mf env lf in
	let cst = Constraint.union cst1 (Constraint.union cst2 cst3) in
        (type_of_case env Evd.empty pj cj lfj, cst)
  
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
  let (j,_) = execute mf env constr in
  assumption_of_judgment env Evd.empty j


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

let type_of_type env c = 
  let tt = safe_machine_type env c in DOP0 (Sort tt.typ)

let unsafe_type_of env c = 
  let (j,_) = unsafe_machine env c in nf_betaiota env Evd.empty j.uj_type

let unsafe_type_of_type env c = 
  let tt = unsafe_machine_type env c in DOP0 (Sort tt.typ)

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

let add_constant sp ce env =
  let (jb,cst) = safe_machine env ce.const_entry_body in
  let env' = add_constraints cst env in
  let (env'',ty,cst') = 
    match ce.const_entry_type with
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
    Idset.union (global_vars_set ce.const_entry_body) (global_vars_set ty.body)
  in
  let cb = { 
    const_kind = kind_of_path sp;
    const_body = Some ce.const_entry_body;
    const_type = ty;
    const_hyps = keep_hyps (var_context env) ids;
    const_constraints = Constraint.union cst cst';
    const_opaque = false } 
  in
  add_constant sp cb env''

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

(* [for_all_prods p env c] checks a boolean condition [p] on all types
   appearing in products in front of [c]. The boolean condition [p] is a 
   function taking a value of type [typed_type] as argument. *)

let rec for_all_prods p env c =
  match whd_betadeltaiota env Evd.empty c with
    | DOP2(Prod, DOP2(Cast,t,DOP0 (Sort s)), DLAM(name,c)) -> 
	(p (make_typed t s)) &&
	(let ty = { body = t; typ = s } in
	 let env' = Environ.push_rel (name,ty) env in
	 for_all_prods p env' c)
    | DOP2(Prod, b, DLAM(name,c)) -> 
	let (jb,cst) = unsafe_machine env b in
	let var = assumption_of_judgment env Evd.empty jb in
	(p var) &&
	(let env' = Environ.push_rel (name,var) (add_constraints cst env) in
	 for_all_prods p env' c)
    | _ -> true

let is_small_type e c = for_all_prods (fun t -> is_small t.typ) e c

let enforce_type_constructor env univ j cst =
  match whd_betadeltaiota env Evd.empty j.uj_type with
    | DOP0 (Sort (Type uc)) -> 
	Constraint.add (univ,Geq,uc) cst
    | _ -> error "Type of Constructor not well-formed"

let type_one_constructor env_ar nparams ar c =
  let (params,dc) = mind_extract_params nparams c in
  let env_par = push_rels params env_ar in
  let (jc,cst) = safe_machine env_par dc in
  let cst' = match sort_of_arity env_ar ar with
    | Type u -> enforce_type_constructor env_par u jc cst
    | Prop _ -> cst
  in
  let (j,cst'') = safe_machine env_ar c in
  let issmall = is_small_type env_par c in
  ((issmall,j), Constraint.union cst' cst'')

let logic_constr env c =
  for_all_prods (fun t -> not (is_info_type env Evd.empty t)) env c

let logic_arity env c =
  for_all_prods 
    (fun t -> 
       (not (is_info_type env Evd.empty t)) or (is_small_type env t.body)) 
    env c

let is_unit env_par nparams ar spec =
  match decomp_all_DLAMV_name spec with
    | (_,[|c|]) ->
	(let (_,a) = mind_extract_params nparams ar in 
	 logic_arity env_par ar) &&
	(let (_,c') = mind_extract_params nparams c in 
	 logic_constr env_par c')
    | _ -> false

let type_one_inductive i env_ar env_par nparams ninds (id,ar,cnames,spec) =
  let (lna,vc) = decomp_all_DLAMV_name spec in
  let ((issmall,jlc),cst') = 
    List.fold_right
      (fun c ((small,jl),cst) -> 
	 let ((sm,jc),cst') = type_one_constructor env_ar nparams ar c in
	 ((small && sm,jc::jl), Constraint.union cst cst'))
      (Array.to_list vc) 
      ((true,[]),Constraint.empty)
  in
  let castlc = List.map cast_of_judgment jlc in
  let spec' = put_DLAMSV lna (Array.of_list castlc) in
  let isunit = is_unit env_par nparams ar spec in
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
    List.fold_left 
      (fun (i,inds,cst) ind -> 
	 let (ind',cst') = 
	   type_one_inductive i env_arities env_params nparams ninds ind 
	 in
	 (succ i,ind'::inds, Constraint.union cst cst'))
      (1,[],Constraint.empty) 
      mie.mind_entry_inds
  in
  let kind = kind_of_path sp in
  let mib = 
    cci_inductive env env_arities kind nparams mie.mind_entry_finite inds cst
  in
  add_mind sp mib (add_constraints cst env)

let add_constraints = add_constraints

let export = export
let import = import

let env_of_safe_env e = e

(*s Machines with information. *)

type information = Logic | Inf of unsafe_judgment
