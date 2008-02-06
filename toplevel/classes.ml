(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: classes.ml 6748 2005-02-18 22:17:50Z herbelin $ i*)

(*i*)
open Names
open Decl_kinds
open Term
open Termops
open Sign
open Entries
open Evd
open Environ
open Nametab
open Mod_subst
open Util
open Typeclasses_errors
open Typeclasses
open Libnames
open Constrintern
open Rawterm
open Topconstr
(*i*)

open Decl_kinds
open Entries

let hint_db = "typeclass_instances"

let add_instance_hint inst = 
  Auto.add_hints false [hint_db] (Vernacexpr.HintsResolve [CRef (Ident (dummy_loc, inst))])

let declare_instance (_,id) =
  add_instance_hint id

let mismatched_params env n m = mismatched_ctx_inst env Parameters n m
(* let mismatched_defs env n m = mismatched_ctx_inst env Definitions n m *)
let mismatched_props env n m = mismatched_ctx_inst env Properties n m

type binder_list = (identifier located * bool * constr_expr) list

let interp_binders_evars isevars env avoid l =
  List.fold_left
    (fun (env, ids, params) ((loc, i), t) -> 
      let n = Name i in
      let t' = interp_binder_evars isevars env n t in
      let d = (i,None,t') in
	(push_named d env, i :: ids, d::params))
    (env, avoid, []) l

let interp_typeclass_context_evars isevars env avoid l =
  List.fold_left
    (fun (env, ids, params) (iid, bk, l) -> 
      let t' = interp_binder_evars isevars env (snd iid) l in
      let i = match snd iid with
	| Anonymous -> Nameops.next_name_away (Termops.named_hd env t' Anonymous) ids
	| Name id -> id
      in
      let d = (i,None,t') in
	(push_named d env, i :: ids, d::params))
    (env, avoid, []) l

let interp_constrs_evars isevars env avoid l =
  List.fold_left
    (fun (env, ids, params) t -> 
      let t' = interp_binder_evars isevars env Anonymous t in
      let id = Nameops.next_name_away (Termops.named_hd env t' Anonymous) ids in
      let d = (id,None,t') in
	(push_named d env, id :: ids, d::params))
    (env, avoid, []) l

let raw_assum_of_binders k = 
  List.map (fun ((loc,i),t) -> LocalRawAssum ([(loc, Name i)], k, t))

let raw_assum_of_constrs k = 
  List.map2 (fun t (n,_,_) -> LocalRawAssum ([(dummy_loc, Name n)], k, t))

let raw_assum_of_anonymous_constrs k = 
  List.map (fun t -> LocalRawAssum ([(dummy_loc, Anonymous)], k, t))

let decl_expr_of_binders = 
  List.map (fun ((loc,i),t) -> false, Vernacexpr.AssumExpr ((loc, Name i), t))
      
let rec unfold n f acc = 
  match n with 
    | 0 -> f 0 acc
    | n -> unfold (n - 1) f (f n acc)

(* Declare everything in the parameters as implicit, and the class instance as well *)
open Topconstr

let declare_implicit_proj c proj imps sub =
  let len = List.length c.cl_context in
  let (ctx, _) = decompose_prod_n (len + 1) (Typeops.type_of_constant (Global.env()) proj) in
  let expls =
    let rec aux i expls = function
	[] -> expls
      | (Name n, _) :: tl -> 
	  let impl = ExplByPos (i, Some n), (true, true) in
	    aux (succ i) (impl :: List.remove_assoc (ExplByName n) expls) tl
      | (Anonymous,_) :: _ -> assert(false)
    in
      aux 1 [] ctx
  in 
  let expls = expls @ List.map (function (ExplByPos (i, n), f) -> (ExplByPos (succ len + i, n)), f | _ -> assert(false)) imps in
    if sub then add_instance_hint (id_of_label (con_label proj));
    Impargs.declare_manual_implicits true (ConstRef proj) true expls
      
let declare_implicits impls subs cl =
  let projs = Recordops.lookup_projections cl.cl_impl in
    Util.list_iter3
      (fun c imps sub -> 
	match c with 
	  | None -> assert(false)
	  | Some p -> declare_implicit_proj cl p imps sub)
      projs impls subs;
    let len = List.length cl.cl_context in
    let indimps = 
      list_fold_left_i 
	(fun i acc (is, (na, b, t)) -> 
	  if len - i <= cl.cl_params then acc
	  else 
	    match is with
		None | Some (_, false) -> (ExplByPos (i, Some na), (false, true)) :: acc
	      | _ -> acc)
	1 [] (List.rev cl.cl_context)
    in
      Impargs.declare_manual_implicits true (IndRef cl.cl_impl) false indimps

let rel_of_named_context subst l = 
  List.fold_right
    (fun (id, _, t) (ctx, acc) -> (Name id, None, subst_vars acc t) :: ctx, id :: acc)
    l ([], subst)

let ids_of_rel_context subst l = 
  List.fold_right
    (fun (id, _, t) acc -> Nameops.out_name id :: acc)
    l subst

let degenerate_decl (na,b,t) =
  let id = match na with
    | Name id -> id
    | Anonymous -> anomaly "Unnamed record variable" in 
  match b with
    | None -> (id, Entries.LocalAssum t)
    | Some b -> (id, Entries.LocalDef b)


let declare_structure env id idbuild params arity fields =
  let nparams = List.length params and nfields = List.length fields in
  let args = extended_rel_list nfields params in
  let ind = applist (mkRel (1+nparams+nfields), args) in
  let type_constructor = it_mkProd_or_LetIn ind fields in
  let mie_ind =
    { mind_entry_typename = id;
      mind_entry_arity = arity;
      mind_entry_consnames = [idbuild];
      mind_entry_lc = [type_constructor] } in
  let mie =
    { mind_entry_params = List.map degenerate_decl params;
      mind_entry_record = true;
      mind_entry_finite = true;
      mind_entry_inds = [mie_ind] } in
  let kn = Command.declare_mutual_with_eliminations true mie in
  let rsp = (kn,0) in (* This is ind path of idstruc *)
  let kinds,sp_projs = Record.declare_projections rsp (List.map (fun _ -> false) fields) fields in
  let _build = ConstructRef (rsp,1) in
    Recordops.declare_structure(rsp,idbuild,List.rev kinds,List.rev sp_projs);
    rsp

let interp_type_evars evdref env ?(impls=([],[])) typ =
  let typ' = intern_gen true ~impls (Evd.evars_of !evdref) env typ in
  let imps = Implicit_quantifiers.implicits_of_rawterm typ' in
    imps, Pretyping.Default.understand_tcc_evars evdref env Pretyping.IsType typ'

let mk_interning_data env na impls typ =
  let impl = Impargs.compute_implicits_with_manual env typ (Impargs.is_implicit_args()) impls
  in (na, ([], impl, Notation.compute_arguments_scope typ))
    
let interp_fields_evars isevars env avoid l =
  List.fold_left
    (fun (env, uimpls, ids, params, impls) ((loc, i), _, t) -> 
      let impl, t' = interp_type_evars isevars env ~impls t in
      let data = mk_interning_data env i impl t' in
      let d = (i,None,t') in
	(push_named d env, impl :: uimpls, Idset.add i ids, d::params, ([], data :: snd impls)))
    (env, [], avoid, [], ([], [])) l    

let name_typeclass_binder avoid = function
  | LocalRawAssum ([loc, Anonymous], bk, c) ->
      let name = 
	let id = 
	match c with
	    CApp (_, (_, CRef (Ident (loc,id))), _) -> id
	  | _ -> id_of_string "assum"
	in Implicit_quantifiers.make_fresh avoid (Global.env ()) id
      in LocalRawAssum ([loc, Name name], bk, c), Idset.add name avoid
  | x -> x, avoid

let name_typeclass_binders avoid l = 
  let l', avoid = 
    List.fold_left 
      (fun (binders, avoid) b -> let b', avoid = name_typeclass_binder avoid b in
				   b' :: binders, avoid)
      ([], avoid) l
  in List.rev l', avoid

let decompose_named_assum = 
  let rec prodec_rec subst l c =
    match kind_of_term c with
      | Prod (Name na,t,c) -> 
	let decl = (na,None,substl subst t) in
	let subst' = mkVar na :: subst in
	  prodec_rec subst' (add_named_decl decl l) (substl subst' c)
      | Cast (c,_,_)      -> prodec_rec subst l c
      | _               -> l,c
  in prodec_rec [] []
      
let push_named_context = List.fold_right push_named

let new_class id par ar sup props =
  let env0 = Global.env() in
  let isevars = ref (Evd.create_evar_defs Evd.empty) in
  let bound = Implicit_quantifiers.ids_of_list (Termops.ids_of_context env0) in
  let bound, ids = Implicit_quantifiers.free_vars_of_binders ~bound [] (sup @ par) in
  let bound = Idset.union bound (Implicit_quantifiers.ids_of_list ids) in
  let sup, bound = name_typeclass_binders bound sup in
  let supnames = 
    List.fold_left (fun acc b -> 
      match b with
	  LocalRawAssum (nl, _, _) -> nl @ acc
	| LocalRawDef _ -> assert(false))
      [] sup
  in

  (* Interpret the arity *)
  let arity_imps, fullarity = 
    let arity = CSort (fst ar, snd ar) in
    let term = prod_constr_expr (prod_constr_expr arity par) sup in
      interp_type_evars isevars env0 term      
  in
  let ctx_params, arity = decompose_named_assum fullarity in
  let env_params = push_named_context ctx_params env0 in
    
  (* Interpret the definitions and propositions *)
  let env_props, prop_impls, bound, ctx_props, _ = 
    interp_fields_evars isevars env_params bound props 
  in
  let subs = List.map (fun ((loc, id), b, _) -> b) props in
  (* Instantiate evars and check all are resolved *)
  let isevars,_ = Evarconv.consider_remaining_unif_problems env_props !isevars in
  let sigma = Evd.evars_of isevars in
  let ctx_params = Implicit_quantifiers.nf_named_context sigma ctx_params in
  let ctx_props = Implicit_quantifiers.nf_named_context sigma ctx_props in
  let arity = Reductionops.nf_evar sigma arity in
  let ce t = Evarutil.check_evars env0 Evd.empty isevars t in
  let kn = 
    let idb = id_of_string ("Build_" ^ (string_of_id (snd id))) in
    let params, subst = rel_of_named_context [] ctx_params (*  @ ctx_super @ ctx_super_ctx) *) in
    let fields, _ = rel_of_named_context subst ctx_props in
      List.iter (fun (_,c,t) -> ce t; match c with Some c -> ce c | None -> ()) (params @ fields);
      declare_structure env0 (snd id) idb params arity fields
  in
  let ctx_context =
    List.map (fun ((na, b, t) as d) -> 
      match Typeclasses.class_of_constr t with
	| Some cl -> (Some (cl.cl_name, List.exists (fun (_, n) -> n = Name na) supnames), d)
	| None -> (None, d))
      ctx_params
  in
  let k =
    { cl_name = snd id;
      cl_params = List.length par;
      cl_context = ctx_context;
      cl_props = ctx_props;
      cl_impl = kn }
  in
    declare_implicits (List.rev prop_impls) subs k;
    add_class k
    
type binder_def_list = (identifier located * identifier located list * constr_expr) list

let binders_of_lidents l =
  List.map (fun (loc, id) -> LocalRawAssum ([loc, Name id], Default Rawterm.Implicit, CHole (loc, None))) l

let subst_ids_in_named_context subst l =
  let x, _ = 
    List.fold_right
      (fun (id, _, t) (ctx, k) -> (id, None, substn_vars k subst t) :: ctx, succ k)
      l ([], 1)
  in x
    
let subst_one_named inst ids t =
  substnl inst 0 (substn_vars 1 ids t)
      
let subst_named inst subst ctx =
  let ids = List.map (fun (id, _, _) -> id) subst in
  let ctx' = subst_ids_in_named_context ids ctx in
  let ctx', _ =
    List.fold_right
      (fun (id, _, t) (ctx, k) -> (id, None, substnl inst k t) :: ctx, succ k)
      ctx' ([], 0)
  in ctx'

let destClass c = 
  match kind_of_term c with
      App (c, args) -> 
	(match kind_of_term c with
	  | Ind ind -> (try class_of_inductive ind, args with _ -> assert false)
	  | _ -> assert false)
    | _ -> assert false

let infer_super_instances env params params_ctx super =
  let super = subst_named params params_ctx super in
    List.fold_right 
      (fun (na, _, t) (sups, ids, supctx) -> 
	let t = subst_one_named sups ids t in
	let inst = 
	  try resolve_one_typeclass env t 
	  with Not_found -> 
	    let cl, args = destClass t in
	      no_instance (push_named_context supctx env) (dummy_loc, cl.cl_name) (Array.to_list args)
	in
	let d = (na, Some inst, t) in
	  inst :: sups, na :: ids, d :: supctx)
      super ([], [], [])
      
(* let evars_of_context ctx id n env = *)
(*   List.fold_right (fun (na, _, t) (n, env, nc) ->  *)
(*     let b = Evarutil.e_new_evar isevars env ~src:(dummy_loc, ImplicitArg (Ident id, (n * Some na))) t in *)
(*     let d = (na, Some b, t) in *)
(*       (succ n, push_named d env, d :: nc)) *)
(*     ctx (n, env, []) *)

let type_ctx_instance isevars env ctx inst subst =
  List.fold_left2
    (fun (subst, instctx) (na, _, t) ce ->
      let t' = replace_vars subst t in
      let c = interp_casted_constr_evars isevars env ce t' in
      let d = na, Some c, t' in
	(na, c) :: subst, d :: instctx)
    (subst, []) (List.rev ctx) inst

let substitution_of_constrs ctx cstrs =
  List.fold_right2 (fun c (na, _, _) acc -> (na, c) :: acc) cstrs ctx []

let destClassApp cl =
  match cl with
    | CApp (loc, (None,CRef (Ident f)), l) -> f, List.map fst l
    | _ -> raise Not_found

let new_instance ctx (instid, bk, cl) props =
  let env = Global.env() in
  let isevars = ref (Evd.create_evar_defs Evd.empty) in

  let tclass = 
    match bk with
      | Explicit ->
	  let id, par = Implicit_quantifiers.destClassAppExpl cl in
	  let k = 
	    try class_info (snd id)
	    with Not_found -> unbound_class env id
	  in
	  let applen = List.fold_left (fun acc (x, y) -> if y = None then succ acc else acc) 0 par in
	  let needlen = List.fold_left (fun acc (x, y) -> if x = None then succ acc else acc) 0 k.cl_context in
	    if needlen <> applen then 
	      mismatched_params env (List.map fst par) (List.map snd k.cl_context);
	    let pars, _ = Implicit_quantifiers.combine_params Idset.empty (* need no avoid *)
	      (fun avoid (clname, (id, _, t)) -> 
		match clname with 
		    Some (cl, b) -> 
		      let t = 
			if b then 
			  let _k = class_info cl in
			    CHole (Util.dummy_loc, Some Evd.InternalHole) (* (Evd.ImplicitArg (IndRef k.cl_impl, (1, None)))) *)
			else CHole (Util.dummy_loc, None)
		      in t, avoid
		  | None -> failwith ("new instance: under-applied typeclass"))
	      par (List.rev k.cl_context)
	    in Topconstr.CAppExpl (Util.dummy_loc, (None, Ident id), pars)

      | Implicit -> cl
  in
  let k, ctx', subst = 
    let c = abstract_constr_expr tclass ctx in
    let _imps, c' = interp_type_evars isevars env c in
    let ctx, c = decompose_named_assum c' in
      (match kind_of_term c with 
	  App (c, args) -> 
	    let cl = Option.get (class_of_constr c) in
	      cl, ctx, substitution_of_constrs (List.map snd cl.cl_context) (List.rev (Array.to_list args))
	| _ -> 
	    let cl = Option.get (class_of_constr c) in
	      cl, ctx, [])
  in
  let env' = push_named_context ctx' env in
  isevars := Evarutil.nf_evar_defs !isevars;
  let sigma = Evd.evars_of !isevars in
  isevars := resolve_typeclasses env sigma !isevars;
  let sigma = Evd.evars_of !isevars in
  let env' = Implicit_quantifiers.nf_env sigma env' in
  let substctx = Typeclasses.nf_substitution sigma subst in
  let subst, propsctx = 
    let props = 
      List.map (fun (x, l, d) -> 
	Topconstr.abstract_constr_expr d (binders_of_lidents l))
	props
    in
      if List.length props <> List.length k.cl_props then 
	mismatched_props env' props k.cl_props;
      type_ctx_instance isevars env' k.cl_props props substctx
  in
  let app = 
    applistc (mkConstruct (k.cl_impl, 1)) (List.rev_map snd subst)
  in 
  let term = Termops.it_mkNamedLambda_or_LetIn app ctx' in
  isevars := Evarutil.nf_evar_defs !isevars;
  let term = Evarutil.nf_isevar !isevars term in
  let cdecl = 
    let kind = IsDefinition Instance in
    let entry = 
      { const_entry_body   = term;
	const_entry_type   = None;
	const_entry_opaque = false;
	const_entry_boxed  = false }
    in DefinitionEntry entry, kind
  in
  let id, cst =
    let instid = 
      match snd instid with
	  Name id -> id
	| Anonymous -> 
	    let i = Nameops.add_suffix k.cl_name "_instance_" in
	      Termops.next_global_ident_away false i (Termops.ids_of_context env)
    in
      instid, Declare.declare_constant instid cdecl
  in 
  let inst = 
    { is_class = k;
      is_name = id;
      is_impl = cst;
    }
  in
    add_instance_hint id;
    add_instance inst
     
let goal_kind = Decl_kinds.Global, Decl_kinds.DefinitionBody Decl_kinds.Definition

let solve_by_tac env evd evar evi t =
  let goal = {it = evi; sigma = (Evd.evars_of evd) } in
  let (res, valid) = t goal in 
    if res.it = [] then 
      let prooftree = valid [] in
      let proofterm, obls = Refiner.extract_open_proof res.sigma prooftree in
	if obls = [] then 
	  let evd' = evars_reset_evd res.sigma evd in
	  let evd' = evar_define evar proofterm evd' in
	    evd', true
	else evd, false
    else evd, false

let context l =
  let env = Global.env() in
  let isevars = ref (Evd.create_evar_defs Evd.empty) in
  let avoid = Termops.ids_of_context env in
  let ctx, l = Implicit_quantifiers.resolve_class_binders (vars_of_env env) l in
  let env', avoid, ctx = interp_binders_evars isevars env avoid ctx in
  let env', avoid, l = interp_typeclass_context_evars isevars env' avoid l in
  isevars := Evarutil.nf_evar_defs !isevars;
  let sigma = Evd.evars_of !isevars in
  let fullctx = Implicit_quantifiers.nf_named_context sigma (l @ ctx) in
    List.iter (function (id,_,t) -> 
      Command.declare_one_assumption false (Local (* global *), Definitional) t false (* inline *) (dummy_loc, id))
      (List.rev fullctx)

open Libobject

let module_qualid = qualid_of_dirpath (dirpath_of_string "Coq.Classes.Init")
let tactic_qualid = make_qualid (dirpath_of_string "Coq.Classes.Init") (id_of_string "typeclass_instantiation")
  
let tactic_expr = Tacexpr.TacArg (Tacexpr.Reference (Qualid (dummy_loc, tactic_qualid)))
let tactic = lazy (Tacinterp.interp tactic_expr)

let _ =
  Typeclasses.solve_instanciation_problem :=
    (fun env evd ev evi -> 
      Library.require_library [(dummy_loc, module_qualid)] None; (* may be inefficient *)
      solve_by_tac env evd ev evi (Lazy.force tactic))

let prod = lazy (Coqlib.build_prod ())

let build_conjunction evm =
  List.fold_left
    (fun (acc, evs) (ev, evi)  ->
      if class_of_constr evi.evar_concl <> None then
	mkApp ((Lazy.force prod).Coqlib.typ, [|evi.evar_concl; acc |]), evs
      else acc, Evd.add evs ev evi)
    (Coqlib.build_coq_True (), Evd.empty) evm

let destruct_conjunction evm_list evm evm' term =
  let _, evm =
    List.fold_right
      (fun (ev, evi) (term, evs) ->
	if class_of_constr evi.evar_concl <> None then
	  match kind_of_term term with
	    | App (x, [| _ ; _ ; proof ; term |]) ->
		let evs' = Evd.define evs ev proof in
		  (term, evs')
	    | _ -> assert(false)
	else
	  match (Evd.find evm' ev).evar_body with
	      Evar_empty -> raise Not_found
	    | Evar_defined c ->
		let evs' = Evd.define evs ev c in
		  (term, evs'))
      evm_list (term, evm)
  in evm
 
(* let solve_by_tac env evd evar evi t = *)
(*   let goal = {it = evi; sigma = (Evd.evars_of evd) } in *)
(*   let (res, valid) = t goal in *)
(*     if res.it = [] then *)
(*       let prooftree = valid [] in *)
(*       let proofterm, obls = Refiner.extract_open_proof res.sigma prooftree in *)
(* 	if obls = [] then *)
(* 	  let evd' = evars_reset_evd res.sigma evd in *)
(* 	  let evd' = evar_define evar proofterm evd' in *)
(* 	    evd', true *)
(* 	else evd, false *)
(*     else evd, false *)

let resolve_all_typeclasses env evd =
  let evm = Evd.evars_of evd in
  let evm_list = Evd.to_list evm in
  let goal, typesevm = build_conjunction evm_list in
  let evars = ref (Evd.create_evar_defs typesevm) in
  let term = resolve_one_typeclass_evd env evars goal in
  let evm' = destruct_conjunction evm_list evm (Evd.evars_of !evars) term in
    Evd.create_evar_defs evm'

let _ =
  Typeclasses.solve_instanciations_problem :=
    (fun env evd -> 
      Library.require_library [(dummy_loc, module_qualid)] None; (* may be inefficient *)
      resolve_all_typeclasses env evd)
