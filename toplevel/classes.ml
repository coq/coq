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

let mismatched_params env n m = mismatched_ctx_inst env Parameters n m
(* let mismatched_defs env n m = mismatched_ctx_inst env Definitions n m *)
let mismatched_props env n m = mismatched_ctx_inst env Properties n m

type binder_list = (identifier located * constr_expr) list

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

let declare_implicit_proj c proj imps =
  let len = List.length c.cl_context + List.length c.cl_super + List.length c.cl_params in
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
    Impargs.declare_manual_implicits true (ConstRef proj) true expls
      
let declare_implicits impls cl =
  let projs = Recordops.lookup_projections cl.cl_impl in
    List.iter2 
      (fun c imps -> 
	match c with 
	  | None -> assert(false)
	  | Some p -> declare_implicit_proj cl p imps)
      projs impls;
    let indimps = 
      list_map_i 
	(fun i (na, b, t) -> ExplByPos (i, Some na), (false, true))
	1 (List.rev cl.cl_context)
    in
      Impargs.declare_manual_implicits true (IndRef cl.cl_impl) false indimps

let rel_of_named_context subst l = 
  List.fold_right
    (fun (id, _, t) (ctx, acc) -> (Name id, None, subst_vars acc t) :: ctx, id :: acc)
    l ([], subst)

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
    (fun (env, uimpls, ids, params, impls) ((loc, i), t) -> 
      let impl, t' = interp_type_evars isevars env ~impls t in
      let data = mk_interning_data env i impl t' in
      let d = (i,None,t') in
	(push_named d env, impl :: uimpls, i :: ids, d::params, ([], data :: snd impls)))
    (env, [], avoid, [], ([], [])) l    

let new_class id par ar sup props =
  let env0 = Global.env() in
  let isevars = ref (Evd.create_evar_defs Evd.empty) in
  let avoid = Termops.ids_of_context env0 in

  let env_params, avoid = env0, avoid in

  (* Find the implicitly quantified variables *)
  let gen_ctx, super = Implicit_quantifiers.resolve_class_binders (vars_of_env env0) sup in

  let env_super_ctx, avoid, ctx_super_ctx = interp_binders_evars isevars env_params avoid gen_ctx in
    
  (* Interpret the superclasses constraints *)
  let env_super, avoid, ctx_super0 = 
    interp_typeclass_context_evars isevars env_super_ctx avoid super 
  in

  let env_params, avoid, ctx_params = interp_binders_evars isevars env_super avoid par in

  (* Interpret the arity *)
  let _arity_imps, arity = interp_type_evars isevars env_params (CSort (fst ar, snd ar)) in
    
  (* let fullarity = it_mkProd_or_LetIn (it_mkProd_or_LetIn arity ctx_defs) ctx_params in*)

  (* Interpret the definitions and propositions *)
  let env_props, prop_impls, avoid, ctx_props, _ = 
    interp_fields_evars isevars env_params avoid props 
  in
    
  (* Instantiate evars and check all are resolved *)
  let isevars,_ = Evarconv.consider_remaining_unif_problems env_props !isevars in
  let sigma = Evd.evars_of isevars in
  let ctx_super_ctx = Implicit_quantifiers.nf_named_context sigma ctx_super_ctx in
  let ctx_super = Implicit_quantifiers.nf_named_context sigma ctx_super0 in
  let ctx_params = Implicit_quantifiers.nf_named_context sigma ctx_params in
  let ctx_props = Implicit_quantifiers.nf_named_context sigma ctx_props in
  let arity = Reductionops.nf_evar sigma arity in
  let ce t = Evarutil.check_evars env0 Evd.empty isevars t in
  let kn = 
    let idb = id_of_string ("Build_" ^ (string_of_id (snd id))) in
    let params, subst = rel_of_named_context [] (ctx_params @ ctx_super @ ctx_super_ctx) in
    let fields, _ = rel_of_named_context subst ctx_props in
      List.iter (fun (_,c,t) -> ce t; match c with Some c -> ce c | None -> ()) (params @ fields);
      declare_structure env0 (snd id) idb params arity fields
  in
  let ctx_context, ctx_super = 
    let class_binders, regular_binders = 
      List.partition (fun (na, b, t) -> 
	Typeclasses.class_of_constr t <> None)
	ctx_super_ctx
    in 
      if (ctx_super_ctx = class_binders @ regular_binders) then
	regular_binders, ctx_super @ class_binders
      else ctx_super_ctx, ctx_super
  in
  let k =
    { cl_name = snd id;
      cl_context = ctx_context;
      cl_super = ctx_super;
      cl_params = ctx_params;
      cl_props = ctx_props;
      cl_impl = kn }
  in
    declare_implicits (List.rev prop_impls) k;
    add_class k
    
open Decl_kinds
open Entries

let hint_db = "typeclass_instances"

let add_instance_hint inst = 
  Auto.add_hints false [hint_db] (Vernacexpr.HintsResolve [CRef (Ident (dummy_loc, inst))])

let declare_instance (_,id) =
  add_instance_hint id

type binder_def_list = (identifier located * identifier located list * constr_expr) list

let binders_of_lidents l =
  List.map (fun (loc, id) -> LocalRawAssum ([loc, Name id], Default Rawterm.Implicit, CHole loc)) l

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

let push_named_context = List.fold_right push_named

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

let new_instance sup (instid, bk, cl) props =
  let id, par = destClassApp cl in
  let env = Global.env() in
  let isevars = ref (Evd.create_evar_defs Evd.empty) in
  let avoid = Termops.ids_of_context env in
  let k = 
    try class_info (snd id)
    with Not_found -> unbound_class env id
  in
  let gen_ctx, sup = Implicit_quantifiers.resolve_class_binders (vars_of_env env) sup in
  let env', avoid, genctx = interp_binders_evars isevars env avoid gen_ctx in
  let env', avoid, supctx = interp_typeclass_context_evars isevars env' avoid sup in
  let subst = 
    match bk with
	Explicit ->
	  if List.length par <> List.length k.cl_context + List.length k.cl_params then 
	    mismatched_params env par (k.cl_params @ k.cl_context);
	  let len = List.length k.cl_context in
	  let ctx, par = Util.list_chop len par in
	  let subst, _ = type_ctx_instance isevars env' k.cl_context ctx [] in
	  let subst = 
	    Typeclasses.substitution_of_named_context isevars env' k.cl_name len subst 
	      k.cl_super 
	  in 
	    if List.length par <> List.length k.cl_params then 
	      mismatched_params env par k.cl_params;
	    let subst, par = type_ctx_instance isevars env' k.cl_params par subst in subst

      | Implicit ->
	  let _imps, t' = interp_type_evars isevars env (Topconstr.mkAppC (CRef (Ident id), par)) in
	    match kind_of_term t' with 
		App (c, args) -> 
		  substitution_of_constrs (k.cl_params @ k.cl_super @ k.cl_context) 
		    (List.rev (Array.to_list args))
	      | _ -> assert false
  in
  isevars := Evarutil.nf_evar_defs !isevars;
  let sigma = Evd.evars_of !isevars in
  let env' = Implicit_quantifiers.nf_env sigma env' in
  let subst = Typeclasses.nf_substitution sigma subst in 
  let subst, propsctx = 
    let props = 
      List.map (fun (x, l, d) -> 
	Topconstr.abstract_constr_expr d (binders_of_lidents l))
	props
    in
      if List.length props <> List.length k.cl_props then 
	mismatched_props env' props k.cl_props;
      type_ctx_instance isevars env' k.cl_props props subst
  in
  let app = 
    applistc (mkConstruct (k.cl_impl, 1)) (List.rev_map snd subst)
  in 
  let term = Termops.it_mkNamedLambda_or_LetIn (Termops.it_mkNamedLambda_or_LetIn app supctx) genctx in
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
	    let i = Nameops.add_suffix (snd id) "_instance_" in
	      Termops.next_global_ident_away false i (Termops.ids_of_context env)
    in
      instid, Declare.declare_constant instid cdecl
  in 
  let inst = 
    { is_class = k;
      is_name = id;
(*       is_params = paramsctx; (\* missing gen_ctx *\) *)
(*       is_super = superctx; *)
      is_impl = cst;
(*       is_add_hint = (fun () -> add_instance_hint id); *)
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

(* let init     () = hints := [] *)
(* let freeze   () = !hints *)
(* let unfreeze fs = hints := fs *)

(* let _ = Summary.declare_summary "hints db" *)
(* 	  { Summary.freeze_function   = freeze; *)
(* 	    Summary.unfreeze_function = unfreeze; *)
(* 	    Summary.init_function     = init; *)
(* 	    Summary.survive_module = false; *)
(* 	    Summary.survive_section   = true } *)

open Libobject

(* let cache (_, db) := hints := db *)

(* let (input,output) =  *)
(*   declare_object *)
(*     { (default_object "hints db") with *)
(*       cache_function = cache; *)
(*       load_function = (fun _ -> cache); *)
(*       open_function = (fun _ -> cache); *)
(*       classify_function = (fun (_,x) -> Keep x); *)
(*       export_function = (fun x -> Some x) } *)

let tactic = ref Tacticals.tclIDTAC
let tactic_expr = ref (Obj.magic ())

let set_instantiation_tactic t = 
  tactic := Tacinterp.interp t; tactic_expr := t

let freeze () = !tactic_expr
let unfreeze t = set_instantiation_tactic t
let init () =  
  set_instantiation_tactic (Tacexpr.TacId[]) 

let cache (_, tac) =
  set_instantiation_tactic tac

let _ = 
  Summary.declare_summary "typeclasses instantiation tactic"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_module = true;
      Summary.survive_section = true }

let (input,output) = 
  declare_object
    { (default_object "type classes instantiation tactic state") with
      cache_function = cache;
      load_function = (fun _ -> cache);
      open_function = (fun _ -> cache);
      classify_function = (fun (_,x) -> Keep x);
      export_function = (fun x -> Some x) }

let set_instantiation_tactic t = 
  Lib.add_anonymous_leaf (input t)
  

let initialize () =
  if !tactic_expr = Tacexpr.TacId [] then
    let qualid = (dummy_loc, qualid_of_dirpath (dirpath_of_string "Coq.Classes.Init")) in
      Library.require_library [qualid] None
    
let _ =
  Typeclasses.solve_instanciation_problem :=
    (fun env -> initialize ();
      fun evd ev evi -> 
	solve_by_tac env evd ev evi !tactic)
      
    
