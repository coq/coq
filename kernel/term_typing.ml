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
open Identifier
open Names
open Univ
open Term
open Reduction
open Sign
open Declarations
open Environ
open Type_errors
open Typeops
open Inductive
open Indtypes

(* The typing machine without information. *)

    (* ATTENTION : faudra faire le typage du contexte des Const,
    MutInd et MutConstructsi un jour cela devient des constructions
    arbitraires et non plus des variables *)

let univ_combinator (cst,univ) (j,c') =
  (j,(Constraint.union cst c', merge_constraints c' univ))

let rec execute env cstr cu =
  match kind_of_term cstr with
    | IsMeta _ ->
	anomaly "the kernel does not understand metas"
    | IsEvar _ ->
	anomaly "the kernel does not understand existential variables"

    | IsSort (Prop c) -> 
	(judge_of_prop_contents c, cu)

    | IsSort (Type u) ->
	let inst_u = if u == dummy_univ then new_univ() else u in
	univ_combinator cu (judge_of_type inst_u)

    | IsApp (f,args) ->
	let (j,cu1) = execute env f cu in
        let (jl,cu2) = execute_array env args cu1 in
	univ_combinator cu2
	  (apply_rel_list env Evd.empty false (Array.to_list jl) j)
	    
    | IsLambda (name,c1,c2) -> 
        let (j,cu1) = execute env c1 cu in
        let var = assumption_of_judgment env Evd.empty j in
	let env1 = push_rel_assum (name,var) env in
        let (j',cu2) = execute env1 c2 cu1 in 
        univ_combinator cu2 (abs_rel env1 Evd.empty name var j')
	  
    | IsProd (name,c1,c2) ->
        let (j,cu1) = execute env c1 cu in
        let varj = type_judgment env Evd.empty j in
	let env1 = push_rel_assum (name,varj.utj_val) env in
        let (j',cu2) = execute env1 c2 cu1 in
        let varj' = type_judgment env1 Evd.empty j' in
	univ_combinator cu2
          (gen_rel env1 Evd.empty name varj varj')

    | IsLetIn (name,c1,c2,c3) ->
        let (j,cu1) = execute env (mkCast(c1,c2)) cu in
        let env1 = push_rel_def (name,j.uj_val,j.uj_type) env in
        let (j',cu2) = execute env1 c3 cu1 in
        univ_combinator cu2
          (judge_of_letin env1 Evd.empty name j j')
	  
    | IsCast (c,t) ->
        let (cj,cu1) = execute env c cu in
        let (tj,cu2) = execute env t cu1 in
	let tj = assumption_of_judgment env Evd.empty tj in
	univ_combinator cu2
          (cast_rel env Evd.empty cj tj)

    | IsRel n -> 
	(relative env n, cu)

    | IsVar id -> 
	(make_judge cstr (lookup_named_type id env), cu)

    | IsConst c ->
        (make_judge cstr (type_of_constant env Evd.empty c), cu)

    (* Inductive types *)
    | IsMutInd ind ->
	(make_judge cstr (type_of_inductive env Evd.empty ind), cu)

    | IsMutConstruct c -> 
	(make_judge cstr (type_of_constructor env Evd.empty c), cu)

    | IsMutCase (ci,p,c,lf) ->
        let (cj,cu1) = execute env c cu in
        let (pj,cu2) = execute env p cu1 in
        let (lfj,cu3) = execute_array env lf cu2 in
        univ_combinator cu3
          (judge_of_case env Evd.empty ci pj cj lfj)
  
    | IsFix ((vn,i as vni),recdef) ->
        if array_exists (fun n -> n < 0) vn then
          error "General Fixpoints not allowed";
        let ((_,tys,_ as recdef'),cu1) = execute_fix env recdef cu in
        let fix = (vni,recdef') in
        check_fix env Evd.empty fix;
	(make_judge (mkFix fix) tys.(i), cu1)
	  
    | IsCoFix (i,recdef) ->
        let ((_,tys,_ as recdef'),cu1) = execute_fix env recdef cu in
        let cofix = (i,recdef') in
        check_cofix env Evd.empty cofix;
	(make_judge (mkCoFix cofix) tys.(i), cu1)
	  
and execute_fix env (names,lar,vdef) cu =
  let (larj,cu1) = execute_array env lar cu in
  let lara = Array.map (assumption_of_judgment env Evd.empty) larj in
  let env1 = push_rec_types (names,lara,vdef) env in
  let (vdefj,cu2) = execute_array env1 vdef cu1 in
  let vdefv = Array.map j_val vdefj in
  let cst = type_fixpoint env1 Evd.empty names lara vdefj in
  univ_combinator cu2 ((names,lara,vdefv),cst)

and execute_array env v cu =
  let (jl,cu1) = execute_list env (Array.to_list v) cu in
  (Array.of_list jl, cu1)

and execute_list env l cu =
  match l with
  | [] -> 
      ([], cu)
  | c::r -> 
      let (j,cu1) = execute env c cu in 
      let (jr,cu2) = execute_list env r cu1 in
      (j::jr, cu2)

(* The typed type of a judgment. *)

let execute_type env constr cu = 
  let (j,cu1) = execute env constr cu in
  (type_judgment env Evd.empty j, cu1)

(* Exported machines. *)

let infer env constr =
  let (j,(cst,_)) =
    execute env constr (Constraint.empty, universes env) in
  (j, cst)

let infer_type env constr =
  let (j,(cst,_)) =
    execute_type env constr (Constraint.empty, universes env) in
  (j, cst)


(* Insertion of variables (named and de Bruijn'ed). They are now typed before
   being added to the environment. *)

let push_rel_or_named_def push (id,b) env =
  let (j,cst) = infer env b in
  let env' = add_constraints cst env in
  push (id,j.uj_val,j.uj_type) env'

let push_named_def = push_rel_or_named_def push_named_def
let push_rel_def = push_rel_or_named_def push_rel_def

let push_rel_or_named_assum push (id,t) env =
  let (j,cst) = infer env t in
  let env' = add_constraints cst env in
  let t = assumption_of_judgment env Evd.empty j in
  push (id,t) env'

let push_named_assum = push_rel_or_named_assum push_named_assum
let push_rel_assum = push_rel_or_named_assum push_rel_assum

let push_rels_with_univ vars env =
  List.fold_left (fun env nvar -> push_rel_assum nvar env) env vars

let infer_local_decl env id = function
  | LocalDef c -> 
      let (j,cst) = infer env c in
      (Name id, Some j.uj_val, j.uj_type), cst
  | LocalAssum c ->
      let (j,cst) = infer env c in
      (Name id, None, assumption_of_judgment env Evd.empty j), cst

let infer_local_decls env decls =
  let rec inferec env = function
  | (id, d) :: l -> 
      let env, l, cst1 = inferec env l in
      let d, cst2 = infer_local_decl env id d in
      push_rel d env, d :: l, Constraint.union cst1 cst2
  | [] -> env, [], Constraint.empty in
  inferec env decls

(* Translation of constant entry to constant body. *)

let make_constant_body env (body,typ,cst) =
  let ids = match body with 
    | None -> global_vars_set typ
    | Some b -> Idset.union (global_vars_set b) (global_vars_set typ) in
  let hyps = keep_hyps ids (named_context env) in
    {
      const_body = body;
      const_type = typ;
      const_hyps = hyps;
      const_constraints = cst;
      const_opaque = false } 

let translate_constant env ce = 
  let (body,typ,cst) as body_info = 
    match ce.const_entry_body with
      | None -> 
	  (match ce.const_entry_type with
	     | None -> 
		 anomaly "Term_typing.translate_constant: No body, no type"
	     | Some ty ->
		 let (j,cst) = infer env ty in
		   None, assumption_of_judgment env Evd.empty j, cst
	  )
      | Some b ->
	  let b'=  match ce.const_entry_type with
	    | None -> b
	    | Some ty -> mkCast (b, ty) 
	  in
	  let (j,cst) = infer env b' in
	    Some j.uj_val, j.uj_type, cst
  in
    make_constant_body env body_info 


(* Translation of inductive types. *)

(* This (re)computes informations relevant to extraction and the sort of an
   arity or type constructor; we do not to recompute universes constraints *)

let rec infos_and_sort env t =
  match kind_of_term t with
    | IsProd (name,c1,c2) ->
        let (varj,_) = infer_type env c1 in
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
  let (j,cst) = infer_type env_ar_par c in
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

let translate_mind env mie =
  mind_check_wellformed env mie;

  (* We first type params and arity of each inductive definition *)
  (* This allows to build the environment of arities and to share *)
  (* the set of constraints *)
  let cst, env_arities, rev_params_arity_list =
    List.fold_left
      (fun (cst,env_arities,l) ind ->
         (* Params are typed-checked here *)
	 let params = ind.mind_entry_params in
	 let env_params, params, cst1 = infer_local_decls env params in
         (* Arities (without params) are typed-checked here *)
	 let arity, cst2 = infer_type env_params ind.mind_entry_arity in
	 (* We do not need to generate the universe of full_arity; if
	    later, after the validation of the inductive definition,
	    full_arity is used as argument or subject to cast, an
	    upper universe will be generated *)
	 let id = ind.mind_entry_typename in
	 let full_arity = it_mkProd_or_LetIn arity.utj_val params in
	 Constraint.union cst (Constraint.union cst1 cst2),
	 push_rel_assum (Name (ident_of_label id), full_arity) env_arities,
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

  (* Finally, we build the inductive packet *)
  cci_inductive env env_arities mie.mind_entry_finite inds cst


