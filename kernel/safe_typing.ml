(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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

(* The typing machine without information. *)

let rec execute env cstr =
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
        let (cj,cst1) = execute env c in
        let (pj,cst2) = execute env p in
        let (lfj,cst3) = execute_array env lf in
	let cst = Constraint.union cst1 (Constraint.union cst2 cst3) in
        (type_of_case env Evd.empty ci pj cj lfj, cst)
  
    | IsFix ((vn,i as vni),(lar,lfi,vdef)) ->
        if array_exists (fun n -> n < 0) vn then
          error "General Fixpoints not allowed";
        let (larjv,vdefv,cst) = execute_fix env lar lfi vdef in
	let larv = Array.map body_of_type larjv in
        let fix = (vni,(larv,lfi,vdefv)) in
        check_fix env Evd.empty fix;
	(make_judge (mkFix fix) larjv.(i), cst)
	  
    | IsCoFix (i,(lar,lfi,vdef)) ->
        let (larjv,vdefv,cst) = execute_fix env lar lfi vdef in
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
	let (j,cst1) = execute env f in
        let (jl,cst2) = execute_array env args in
	let (j,cst3) =
	  apply_rel_list env Evd.empty false (Array.to_list jl) j in
	let cst = Constraint.union cst1 (Constraint.union cst2 cst3) in
	(j, cst)
	    
    | IsLambda (name,c1,c2) -> 
        let (j,cst1) = execute env c1 in
        let var = assumption_of_judgment env Evd.empty j in
	let env1 = push_rel_assum (name,var) env in
        let (j',cst2) = execute env1 c2 in 
        let (j,cst3) = abs_rel env1 Evd.empty name var j' in
	let cst = Constraint.union cst1 (Constraint.union cst2 cst3) in
	(j, cst)
	  
     | IsProd (name,c1,c2) ->
        let (j,cst1) = execute env c1 in
        let varj = type_judgment env Evd.empty j in
	let env1 = push_rel_assum (name,varj.utj_val) env in
        let (j',cst2) = execute env1 c2 in
        let varj' = type_judgment env Evd.empty j' in
	let (j,cst3) = gen_rel env1 Evd.empty name varj varj' in
	let cst = Constraint.union cst1 (Constraint.union cst2 cst3) in
	(j, cst)

     | IsLetIn (name,c1,c2,c3) ->
        let (j1,cst1) = execute env c1 in
        let (j2,cst2) = execute env c2 in
	let tj2 = assumption_of_judgment env Evd.empty j2 in
	let ({uj_val = b; uj_type = t},cst0) = cast_rel env Evd.empty j1 tj2 in
        let (j3,cst3) = execute (push_rel_def (name,b,t) env) c3 in
	let cst = Constraint.union cst1 (Constraint.union cst2 cst3) in
	({ uj_val = mkLetIn (name, j1.uj_val, tj2, j3.uj_val) ;
	   uj_type = type_app (subst1 j1.uj_val) j3.uj_type },
	 Constraint.union cst cst0)
	  
    | IsCast (c,t) ->
        let (cj,cst1) = execute env c in
        let (tj,cst2) = execute env t in
	let tj = assumption_of_judgment env Evd.empty tj in
	let cst = Constraint.union cst1 cst2 in
	let (j, cst0) = cast_rel env Evd.empty cj tj in
	(j, Constraint.union cst cst0)
	  
and execute_fix env lar lfi vdef =
  let (larj,cst1) = execute_array env lar in
  let lara = Array.map (assumption_of_judgment env Evd.empty) larj in
  let nlara = 
    List.combine (List.rev lfi) (Array.to_list (vect_lift_type lara)) in
  let env1 = 
    List.fold_left (fun env nvar -> push_rel_assum nvar env) env nlara in
  let (vdefj,cst2) = execute_array env1 vdef in
  let vdefv = Array.map j_val vdefj in
  let cst3 = type_fixpoint env1 Evd.empty lfi lara vdefj in
  let cst = Constraint.union cst1 (Constraint.union cst2 cst3) in
  (lara,vdefv,cst)

and execute_array env v =
  let (jl,u1) = execute_list env (Array.to_list v) in
  (Array.of_list jl, u1)

and execute_list env = function
  | [] -> 
      ([], Constraint.empty)
  | c::r -> 
      let (j,cst1) = execute env c in 
      let (jr,cst2) = execute_list env r in
      (j::jr, Constraint.union cst1 cst2)

(* The typed type of a judgment. *)

let execute_type env constr = 
  let (j,cst) = execute env constr in
  (type_judgment env Evd.empty j, cst)

(* Renaming for the following. *)

let safe_infer = execute

let safe_infer_type = execute_type

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

let safe_infer_local_decl env id = function
  | LocalDef c -> 
      let (j,cst) = safe_infer env c in
      (Name id, Some j.uj_val, j.uj_type), cst
  | LocalAssum c ->
      let (j,cst) = safe_infer env c in
      (Name id, None, assumption_of_judgment env Evd.empty j), cst

let safe_infer_local_decls env decls =
  let rec inferec env = function
  | (id, d) :: l -> 
      let env, l, cst1 = inferec env l in
      let d, cst2 = safe_infer_local_decl env id d in
      push_rel d env, d :: l, Constraint.union cst1 cst2
  | [] -> env, [], Constraint.empty in
  inferec env decls

(* Insertion of constants and parameters in environment. *)
type global_declaration = Def of constr | Assum of constr

let safe_infer_declaration env = function
  | Def c ->
      let (j,cst) = safe_infer env c in
      Some j.uj_val, j.uj_type, cst
  | Assum t ->
      let (j,cst) = safe_infer env t in
      None, assumption_of_judgment env Evd.empty j, cst

type local_names = (identifier * variable_path) list

let add_global_declaration sp env locals (body,typ,cst) =
  let env' = add_constraints cst env in
  let ids = match body with 
    | None -> global_vars_set typ
    | Some b -> Idset.union (global_vars_set b) (global_vars_set typ) in
  let hyps = keep_hyps ids (named_context env) in
  let body, typ =
    if Options.immediate_discharge then
      option_app (fun c -> it_mkNamedLambda_or_LetIn c hyps) body,
      it_mkNamedProd_or_LetIn typ hyps
    else
      body,typ in
  let sp_hyps = List.map (fun (id,b,t) -> (List.assoc id locals, b, t)) hyps in
  let cb = {
    const_kind = kind_of_path sp;
    const_body = body;
    const_type = typ;
    const_hyps = sp_hyps;
    const_constraints = cst;
    const_opaque = false } 
  in
  Environ.add_constant sp cb env'

let add_parameter sp t locals env =
  add_global_declaration sp env locals (safe_infer_declaration env (Assum t))

let add_constant_with_value sp body typ locals env =
  let body' =
    match typ with
      | None -> body
      | Some ty -> mkCast (body, ty) in
  add_global_declaration sp env locals (safe_infer_declaration env (Def body'))

let add_constant sp ce locals env =
  add_constant_with_value sp ce.const_entry_body ce.const_entry_type locals env

let add_discharged_constant sp r locals env =
  let (body,typ) = Cooking.cook_constant env r in
  match body with
    | None -> 
	add_parameter sp typ locals (* Bricolage avant poubelle *) env
    | Some c -> 
	(* let c = hcons1_constr c in *)
	let (jtyp,cst) = safe_infer env typ in
	let env' = add_constraints cst env in
	let ids = 
	  Idset.union (global_vars_set c) 
	    (global_vars_set (body_of_type jtyp.uj_val))
	in
	let hyps = keep_hyps ids (named_context env) in
	let sp_hyps =
	  List.map (fun (id,b,t) -> (List.assoc id locals,b,t)) hyps in
	let cb =
	  { const_kind = kind_of_path sp;
	    const_body = Some c;
	    const_type = assumption_of_judgment env' Evd.empty jtyp;
	    const_hyps = sp_hyps;
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

let small_unit constrsinfos (env_ar_par,short_arity) =
  let issmall = List.for_all is_small constrsinfos in
  let arinfos = infos_and_sort env_ar_par short_arity in
  let isunit = is_unit arinfos constrsinfos in
  issmall, isunit

(* [smax] is the max of the sorts of the products of the constructor type *)

let enforce_type_constructor arsort smax cst =
  match smax, arsort with
    | Type uc, Type ua -> Constraint.add (ua,Geq,uc) cst
    | _,_ -> cst

let type_one_constructor env_ar_par params arsort c =
  let infos = infos_and_sort env_ar_par c in

  (* Each constructor is typed-checked here *)
  let (j,cst) = safe_infer_type env_ar_par c in
  let full_cstr_type = it_mkProd_or_LetIn j.utj_val params in

  (* If the arity is at some level Type arsort, then the sort of the
     constructor must be below arsort; here we consider constructors with the
     global parameters (which add a priori more constraints on their sort) *)
  let cst2 = enforce_type_constructor arsort j.utj_type cst in

  (infos, full_cstr_type, cst2)

let infer_constructor_packet env_ar params short_arity arsort vc =
  let env_ar_par = push_rels params env_ar in
  let (constrsinfos,jlc,cst) = 
    List.fold_right
      (fun c (infosl,l,cst) ->
	 let (infos,ct,cst') =
	   type_one_constructor env_ar_par params arsort c in
	 (infos::infosl,ct::l, Constraint.union cst cst'))
      vc
      ([],[],Constraint.empty) in
  let vc' = Array.of_list jlc in
  let issmall,isunit = small_unit constrsinfos (env_ar_par,short_arity) in
  (issmall,isunit,vc', cst)

let add_mind sp mie locals env =
  mind_check_wellformed env mie;

  (* We first type params and arity of each inductive definition *)
  (* This allows to build the environment of arities and to share *)
  (* the set of constraints *)
  let cst, env_arities, rev_params_arity_list =
    List.fold_left
      (fun (cst,env_arities,l) ind ->
         (* Params are typed-checked here *)
	 let params = ind.mind_entry_params in
	 let env_params, params, cst1 = safe_infer_local_decls env params in
         (* Arities (without params) are typed-checked here *)
	 let arity, cst2 = safe_infer_type env_params ind.mind_entry_arity in
	 (* We do not need to generate the universe of full_arity; if
	    later, after the validation of the inductive definition,
	    full_arity is used as argument or subject to cast, an
	    upper universe will be generated *)
	 let id = ind.mind_entry_typename in
	 let full_arity = it_mkProd_or_LetIn arity.utj_val params in
	 Constraint.union cst (Constraint.union cst1 cst2),
	 push_rel_assum (Name id, full_arity) env_arities,
         (params, id, full_arity, arity.utj_val)::l)
      (Constraint.empty,env,[])
      mie.mind_entry_inds in

  let params_arity_list = List.rev rev_params_arity_list in

  (* Now, we type the constructors (without params) *)
  let inds,cst =
    List.fold_right2
      (fun ind (params,id,full_arity,short_arity) (inds,cst) ->
	 let arsort = sort_of_arity env full_arity in
	 let lc = ind.mind_entry_lc in
	 let (issmall,isunit,lc',cst') =
	   infer_constructor_packet env_arities params short_arity arsort lc
	 in
	 let nparams = ind.mind_entry_nparams in
	 let consnames = ind.mind_entry_consnames in
	 let ind' = (params,nparams,id,full_arity,consnames,issmall,isunit,lc')
	 in
	 (ind'::inds, Constraint.union cst cst'))
      mie.mind_entry_inds
      params_arity_list
      ([],cst) in

  (* Finally, we build the inductive packet and push it to env *)
  let kind = kind_of_path sp in
  let mib = cci_inductive locals env env_arities kind mie.mind_entry_finite inds cst
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

(* Exported typing functions *)

let typing env c = 
  let (j,cst) = safe_infer env c in
  let _ = add_constraints cst env in
  j

let typing_in_unsafe_env = typing
