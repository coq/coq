(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Names
open Term
open Vars
open Environ
open Nametab
open Errors
open Util
open Typeclasses_errors
open Typeclasses
open Libnames
open Globnames
open Constrintern
open Constrexpr
(*i*)

open Decl_kinds
open Entries

let typeclasses_db = "typeclass_instances"

let set_typeclass_transparency c local b = 
  Auto.add_hints local [typeclasses_db] 
    (Auto.HintsTransparencyEntry ([c], b))
    
let _ =
  Hook.set Typeclasses.add_instance_hint_hook
    (fun inst path local pri ->
      Flags.silently (fun () ->
	Auto.add_hints local [typeclasses_db]
	  (Auto.HintsResolveEntry
	     [pri, false, Auto.PathHints path, inst])) ());
  Hook.set Typeclasses.set_typeclass_transparency_hook set_typeclass_transparency;
  Hook.set Typeclasses.classes_transparent_state_hook
    (fun () -> Auto.Hint_db.transparent_state (Auto.searchtable_map typeclasses_db))
    
let declare_class g =
  match global g with
  | ConstRef x -> Typeclasses.add_constant_class x
  | IndRef x -> Typeclasses.add_inductive_class x
  | _ -> user_err_loc (loc_of_reference g, "declare_class", 
		      Pp.str"Unsupported class type, only constants and inductives are allowed")
    
(** TODO: add subinstances *)
let existing_instance glob g pri =
  let c = global g in
  let instance = Typing.type_of (Global.env ()) Evd.empty (constr_of_global c) in
  let _, r = decompose_prod_assum instance in
    match class_of_constr r with
      | Some (_, (tc, _)) -> add_instance (new_instance tc pri glob c)
      | None -> user_err_loc (loc_of_reference g, "declare_instance",
			     Pp.str "Constant does not build instances of a declared type class.")

let mismatched_params env n m = mismatched_ctx_inst env Parameters n m
let mismatched_props env n m = mismatched_ctx_inst env Properties n m

(* Declare everything in the parameters as implicit, and the class instance as well *)

let type_ctx_instance evars env ctx inst subst =
  let rec aux (subst, instctx) l = function
    (na, b, t) :: ctx ->
      let t' = substl subst t in
      let c', l =
	match b with
	| None -> interp_casted_constr_evars evars env (List.hd l) t', List.tl l
	| Some b -> substl subst b, l
      in
      let d = na, Some c', t' in
	aux (c' :: subst, d :: instctx) l ctx
    | [] -> subst
  in aux (subst, []) inst (List.rev ctx)

let refine_ref = ref (fun _ -> assert(false))

let id_of_class cl =
  match cl.cl_impl with
    | ConstRef kn -> let _,_,l = repr_con kn in Label.to_id l
    | IndRef (kn,i) ->
	let mip = (Environ.lookup_mind kn (Global.env ())).Declarations.mind_packets in
	  mip.(0).Declarations.mind_typename
    | _ -> assert false

open Pp

let instance_hook k pri global imps ?hook cst =
  Impargs.maybe_declare_manual_implicits false cst ~enriching:false imps;
  Typeclasses.declare_instance pri (not global) cst;
  (match hook with Some h -> h cst | None -> ())

let declare_instance_constant k pri global imps ?hook id term termtype =
  let kind = IsDefinition Instance in
  let entry = {
    const_entry_body   = Future.from_val term;
    const_entry_secctx = None;
    const_entry_type   = Some termtype;
    const_entry_opaque = false;
    const_entry_inline_code = false;
    const_entry_feedback = None;
  } in
  let cdecl = (DefinitionEntry entry, kind) in
  let kn = Declare.declare_constant id cdecl in
    Declare.definition_message id;
    instance_hook k pri global imps ?hook (ConstRef kn);
    id

let new_instance ?(abstract=false) ?(global=false) ctx (instid, bk, cl) props
    ?(generalize=true)
    ?(tac:unit Proofview.tactic option) ?hook pri =
  let env = Global.env() in
  let evars = ref Evd.empty in
  let tclass, ids =
    match bk with
    | Implicit ->
	Implicit_quantifiers.implicit_application Id.Set.empty ~allow_partial:false
	  (fun avoid (clname, (id, _, t)) ->
	    match clname with
	    | Some (cl, b) ->
		let t = CHole (Loc.ghost, None, None) in
		  t, avoid
	    | None -> failwith ("new instance: under-applied typeclass"))
	  cl
    | Explicit -> cl, Id.Set.empty
  in
  let tclass = if generalize then CGeneralization (Loc.ghost, Implicit, Some AbsPi, tclass) else tclass in
  let k, cty, ctx', ctx, len, imps, subst =
    let impls, ((env', ctx), imps) = interp_context_evars evars env ctx in
    let c', imps' = interp_type_evars_impls ~impls evars env' tclass in
    let len = List.length ctx in
    let imps = imps @ Impargs.lift_implicits len imps' in
    let ctx', c = decompose_prod_assum c' in
    let ctx'' = ctx' @ ctx in
    let cl, args = Typeclasses.dest_class_app (push_rel_context ctx'' env) c in
    let _, args = 
      List.fold_right (fun (na, b, t) (args, args') ->
	match b with
	| None -> (List.tl args, List.hd args :: args')
	| Some b -> (args, substl args' b :: args'))
	(snd cl.cl_context) (args, [])
    in
      cl, c', ctx', ctx, len, imps, args
  in
  let id =
    match snd instid with
	Name id ->
	  let sp = Lib.make_path id in
	    if Nametab.exists_cci sp then
	      errorlabstrm "new_instance" (Nameops.pr_id id ++ Pp.str " already exists.");
	    id
      | Anonymous ->
	  let i = Nameops.add_suffix (id_of_class k) "_instance_0" in
	    Namegen.next_global_ident_away i (Termops.ids_of_context env)
  in
  let env' = push_rel_context ctx env in
  evars := Evarutil.nf_evar_map !evars;
  evars := resolve_typeclasses ~filter:Typeclasses.no_goals ~fail:true env !evars;
  let sigma =  !evars in
  let subst = List.map (Evarutil.nf_evar sigma) subst in
    if abstract then
      begin
	let _, ty_constr = instance_constructor k (List.rev subst) in
	let termtype =
	  let t = it_mkProd_or_LetIn ty_constr (ctx' @ ctx) in
	    Evarutil.nf_evar !evars t
	in
	Evarutil.check_evars env Evd.empty !evars termtype;
	let cst = Declare.declare_constant ~internal:Declare.KernelSilent id
	  (Entries.ParameterEntry 
            (None,termtype,None), Decl_kinds.IsAssumption Decl_kinds.Logical)
	in instance_hook k None global imps ?hook (ConstRef cst); id
      end
    else (
      let props =
	match props with
	| Some (CRecord (loc, _, fs)) ->
	    if List.length fs > List.length k.cl_props then
	      mismatched_props env' (List.map snd fs) k.cl_props;
	    Some (Inl fs)
	| Some t -> Some (Inr t)
	| None -> 
	    if Flags.is_program_mode () then Some (Inl [])
	    else None
      in
      let subst =
	match props with
	| None -> if List.is_empty k.cl_props then Some (Inl subst) else None
	| Some (Inr term) ->
	    let c = interp_casted_constr_evars evars env' term cty in
	      Some (Inr (c, subst))
	| Some (Inl props) ->
	    let get_id =
	      function
		| Ident id' -> id'
		| _ -> errorlabstrm "new_instance" (Pp.str "Only local structures are handled")
	    in
	    let props, rest =
	      List.fold_left
		(fun (props, rest) (id,b,_) ->
		   if Option.is_empty b then
		     try
                      let is_id (id', _) = match id, get_id id' with
                      | Name id, (_, id') -> Id.equal id id'
                      | Anonymous, _ -> false
                      in
		       let (loc_mid, c) =
			 List.find is_id rest 
		       in
		       let rest' = 
			 List.filter (fun v -> not (is_id v)) rest 
		       in
		       let (loc, mid) = get_id loc_mid in
			 List.iter (fun (n, _, x) -> 
				      if Name.equal n (Name mid) then
					Option.iter (fun x -> Dumpglob.add_glob loc (ConstRef x)) x)
			   k.cl_projs;
			 c :: props, rest'
		     with Not_found ->
		       (CHole (Loc.ghost, Some Evar_kinds.GoalEvar, None) :: props), rest
		   else props, rest)
		([], props) k.cl_props
	    in
              match rest with
              | (n, _) :: _ ->
		unbound_method env' k.cl_impl (get_id n)
              | _ ->
		Some (Inl (type_ctx_instance evars (push_rel_context ctx' env') 
			     k.cl_props props subst))
      in	  
      let term, termtype =
	match subst with
	| None -> let termtype = it_mkProd_or_LetIn cty ctx in
	    None, termtype
	| Some (Inl subst) ->
	  let subst = List.fold_left2
	    (fun subst' s (_, b, _) -> if Option.is_empty b then s :: subst' else subst')
	    [] subst (k.cl_props @ snd k.cl_context)
	  in
	  let app, ty_constr = instance_constructor k subst in
	  let termtype = it_mkProd_or_LetIn ty_constr (ctx' @ ctx) in
	  let term = Termops.it_mkLambda_or_LetIn (Option.get app) (ctx' @ ctx) in
	    Some term, termtype
	| Some (Inr (def, subst)) ->
	  let termtype = it_mkProd_or_LetIn cty ctx in
	  let term = Termops.it_mkLambda_or_LetIn def ctx in
	    Some term, termtype
      in
      let _ = 
	evars := Evarutil.nf_evar_map !evars;
	evars := Typeclasses.resolve_typeclasses ~filter:Typeclasses.no_goals_or_obligations ~fail:true
          env !evars;
	(* Try resolving fields that are typeclasses automatically. *)
	evars := Typeclasses.resolve_typeclasses ~filter:Typeclasses.all_evars ~fail:false
	  env !evars
      in
      let termtype = Evarutil.nf_evar !evars termtype in
      let _ = (* Check that the type is free of evars now. *)
	Evarutil.check_evars env Evd.empty !evars termtype
      in
      let term = Option.map (Evarutil.nf_evar !evars) term in
      let evm = Evarutil.nf_evar_map_undefined !evars in
	if not (Evd.has_undefined evm) && not (Option.is_empty term) then
	  declare_instance_constant k pri global imps ?hook id 
            (Option.get term,Declareops.no_seff) termtype
	else begin
	  let kind = Decl_kinds.Global, Decl_kinds.DefinitionBody Decl_kinds.Instance in
	    if Flags.is_program_mode () then
	      let hook vis gr =
		let cst = match gr with ConstRef kn -> kn | _ -> assert false in
		  Impargs.declare_manual_implicits false gr ~enriching:false [imps];
		  Typeclasses.declare_instance pri (not global) (ConstRef cst)
	      in
	      let obls, constr, typ =
		match term with 
		| Some t -> 
		  let obls, _, constr, typ = 
		    Obligations.eterm_obligations env id !evars 0 t termtype
		  in obls, Some constr, typ
		| None -> [||], None, termtype
	      in
		ignore (Obligations.add_definition id ?term:constr
			typ ~kind:(Global,Instance) ~hook obls);
		id
	    else
	      (Flags.silently 
	       (fun () ->
		Lemmas.start_proof id kind termtype
		(fun _ -> instance_hook k pri global imps ?hook);
                 (* spiwack: I don't know what to do with the status here. *)
		if not (Option.is_empty term) then 
		  ignore (Pfedit.by (!refine_ref (evm, Option.get term)))
		else if Flags.is_auto_intros () then
		  ignore (Pfedit.by (Tacticals.New.tclDO len Tactics.intro));
		(match tac with Some tac -> ignore (Pfedit.by tac) | None -> ())) ();
	       id)
	end)
	
let named_of_rel_context l =
  let acc, ctx =
    List.fold_right
      (fun (na, b, t) (subst, ctx) ->
	let id = match na with Anonymous -> invalid_arg "named_of_rel_context" | Name id -> id in
	let d = (id, Option.map (substl subst) b, substl subst t) in
	  (mkVar id :: subst, d :: ctx))
      l ([], [])
  in ctx

let context l =
  let env = Global.env() in
  let evars = ref Evd.empty in
  let _, ((env', fullctx), impls) = interp_context_evars evars env l in
  let fullctx = Evarutil.nf_rel_context_evar !evars fullctx in
  let ce t = Evarutil.check_evars env Evd.empty !evars t in
  let () = List.iter (fun (n, b, t) -> Option.iter ce b; ce t) fullctx in
  let ctx =
    try named_of_rel_context fullctx
    with e when Errors.noncritical e ->
      error "Anonymous variables not allowed in contexts."
  in
  let fn status (id, _, t) =
    if Lib.is_modtype () && not (Lib.sections_are_opened ()) then
      let decl = (ParameterEntry (None,t,None), IsAssumption Logical) in
      let cst = Declare.declare_constant ~internal:Declare.KernelSilent id decl in
	match class_of_constr t with
	| Some (rels, (tc, args) as _cl) ->
	    add_instance (Typeclasses.new_instance tc None false (ConstRef cst));
            status
	    (* declare_subclasses (ConstRef cst) cl *)
	| None -> status
    else
      let test (x, _) = match x with
      | ExplByPos (_, Some id') -> Id.equal id id'
      | _ -> false
      in
      let impl = List.exists test impls in
      let decl = (Discharge, Definitional) in
      let nstatus =
        snd (Command.declare_assumption false decl t [] impl
          Vernacexpr.NoInline (Loc.ghost, id))
      in
      status && nstatus
  in List.fold_left fn true (List.rev ctx)
