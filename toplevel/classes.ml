(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
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
open CErrors
open Util
open Typeclasses_errors
open Typeclasses
open Libnames
open Globnames
open Constrintern
open Constrexpr
open Sigma.Notations
open Context.Rel.Declaration
(*i*)

open Decl_kinds
open Entries

let refine_instance = ref true

let _ = Goptions.declare_bool_option {
  Goptions.optsync  = true;
  Goptions.optdepr  = false;
  Goptions.optname  = "definition of instances by refining";
  Goptions.optkey   = ["Refine";"Instance";"Mode"];
  Goptions.optread  = (fun () -> !refine_instance);
  Goptions.optwrite = (fun b -> refine_instance := b)
}

let typeclasses_db = "typeclass_instances"

let set_typeclass_transparency c local b = 
  Hints.add_hints local [typeclasses_db] 
    (Hints.HintsTransparencyEntry ([c], b))
    
let _ =
  Hook.set Typeclasses.add_instance_hint_hook
    (fun inst path local pri poly ->
     let inst' = match inst with IsConstr c -> Hints.IsConstr (c, Univ.ContextSet.empty)
       | IsGlobal gr -> Hints.IsGlobRef gr
     in
      Flags.silently (fun () ->
	Hints.add_hints local [typeclasses_db]
	  (Hints.HintsResolveEntry
	     [pri, poly, false, Hints.PathHints path, inst'])) ());
  Hook.set Typeclasses.set_typeclass_transparency_hook set_typeclass_transparency;
  Hook.set Typeclasses.classes_transparent_state_hook
    (fun () -> Hints.Hint_db.transparent_state (Hints.searchtable_map typeclasses_db))
        
(** TODO: add subinstances *)
let existing_instance glob g pri =
  let c = global g in
  let instance = Global.type_of_global_unsafe c in
  let _, r = decompose_prod_assum instance in
    match class_of_constr r with
      | Some (_, ((tc,u), _)) -> add_instance (new_instance tc pri glob 
  (*FIXME*) (Flags.use_polymorphic_flag ()) c)
      | None -> user_err_loc (loc_of_reference g, "declare_instance",
			     Pp.str "Constant does not build instances of a declared type class.")

let mismatched_params env n m = mismatched_ctx_inst env Parameters n m
let mismatched_props env n m = mismatched_ctx_inst env Properties n m

(* Declare everything in the parameters as implicit, and the class instance as well *)

let type_ctx_instance evars env ctx inst subst =
  let rec aux (subst, instctx) l = function
    decl :: ctx ->
      let t' = substl subst (get_type decl) in
      let c', l =
	match decl with
	| LocalAssum _ -> interp_casted_constr_evars env evars (List.hd l) t', List.tl l
	| LocalDef (_,b,_) -> substl subst b, l
      in
      let d = get_name decl, Some c', t' in
	aux (c' :: subst, d :: instctx) l ctx
    | [] -> subst
  in aux (subst, []) inst (List.rev ctx)

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

let declare_instance_constant k pri global imps ?hook id pl poly evm term termtype =
  let kind = IsDefinition Instance in
  let evm = 
    let levels = Univ.LSet.union (Universes.universes_of_constr termtype) 
				 (Universes.universes_of_constr term) in
    Evd.restrict_universe_context evm levels 
  in
  let pl, uctx = Evd.universe_context ?names:pl evm in
  let entry = 
    Declare.definition_entry ~types:termtype ~poly ~univs:uctx term
  in
  let cdecl = (DefinitionEntry entry, kind) in
  let kn = Declare.declare_constant id cdecl in
    Declare.definition_message id;
    Universes.register_universe_binders (ConstRef kn) pl;
    instance_hook k pri global imps ?hook (ConstRef kn);
    id

let new_instance ?(abstract=false) ?(global=false) ?(refine= !refine_instance) poly ctx (instid, bk, cl) props
    ?(generalize=true)
    ?(tac:unit Proofview.tactic option) ?hook pri =
  let env = Global.env() in
  let ((loc, instid), pl) = instid in
  let uctx = Evd.make_evar_universe_context env pl in
  let evars = ref (Evd.from_ctx uctx) in
  let tclass, ids =
    match bk with
    | Implicit ->
	Implicit_quantifiers.implicit_application Id.Set.empty ~allow_partial:false
	  (fun avoid (clname, _) ->
	    match clname with
	    | Some (cl, b) ->
		let t = CHole (Loc.ghost, None, Misctypes.IntroAnonymous, None) in
		  t, avoid
	    | None -> failwith ("new instance: under-applied typeclass"))
	  cl
    | Explicit -> cl, Id.Set.empty
  in
  let tclass = 
    if generalize then CGeneralization (Loc.ghost, Implicit, Some AbsPi, tclass) 
    else tclass 
  in
  let k, u, cty, ctx', ctx, len, imps, subst =
    let impls, ((env', ctx), imps) = interp_context_evars env evars ctx in
    let c', imps' = interp_type_evars_impls ~impls env' evars tclass in
    let len = List.length ctx in
    let imps = imps @ Impargs.lift_implicits len imps' in
    let ctx', c = decompose_prod_assum c' in
    let ctx'' = ctx' @ ctx in
    let k, args = Typeclasses.dest_class_app (push_rel_context ctx'' env) c in
    let cl, u = Typeclasses.typeclass_univ_instance k in
    let _, args = 
      List.fold_right (fun decl (args, args') ->
        let open Context.Rel.Declaration in
	match decl with
	| LocalAssum _ -> (List.tl args, List.hd args :: args')
	| LocalDef (_,b,_) -> (args, substl args' b :: args'))
	(snd cl.cl_context) (args, [])
    in
      cl, u, c', ctx', ctx, len, imps, args
  in
  let id =
    match instid with
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
  evars := resolve_typeclasses ~filter:Typeclasses.all_evars ~fail:true env !evars;
  let subst = List.map (Evarutil.nf_evar !evars) subst in
    if abstract then
      begin
	let subst = List.fold_left2
	  (fun subst' s decl -> if is_local_assum decl then s :: subst' else subst')
	  [] subst (snd k.cl_context)
	in
	let (_, ty_constr) = instance_constructor (k,u) subst in
	let nf, subst = Evarutil.e_nf_evars_and_universes evars in
	let termtype =
	  let t = it_mkProd_or_LetIn ty_constr (ctx' @ ctx) in
	    nf t
	in
	Pretyping.check_evars env Evd.empty !evars termtype;
	let pl, ctx = Evd.universe_context ?names:pl !evars in
	let cst = Declare.declare_constant ~internal:Declare.InternalTacticRequest id
	  (ParameterEntry 
            (None,poly,(termtype,ctx),None), Decl_kinds.IsAssumption Decl_kinds.Logical)
	in
	  Universes.register_universe_binders (ConstRef cst) pl;
	  instance_hook k pri global imps ?hook (ConstRef cst); id
      end
    else (
      let props =
	match props with
	| Some (true, CRecord (loc, fs)) ->
	    if List.length fs > List.length k.cl_props then
	      mismatched_props env' (List.map snd fs) k.cl_props;
	    Some (Inl fs)
	| Some (_, t) -> Some (Inr t)
	| None -> 
	    if Flags.is_program_mode () then Some (Inl [])
	    else None
      in
      let subst =
	match props with
	| None -> if List.is_empty k.cl_props then Some (Inl subst) else None
	| Some (Inr term) ->
	    let c = interp_casted_constr_evars env' evars term cty in
	      Some (Inr (c, subst))
	| Some (Inl props) ->
	    let get_id =
	      function
		| Ident id' -> id'
		| Qualid (loc,id') -> (loc, snd (repr_qualid id'))
	    in
	    let props, rest =
	      List.fold_left
		(fun (props, rest) decl ->
		  if is_local_assum decl then
		    try
		      let is_id (id', _) = match get_name decl, get_id id' with
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
		       (CHole (Loc.ghost, None(* Some Evar_kinds.GoalEvar *), Misctypes.IntroAnonymous, None) :: props), rest
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
	    (fun subst' s decl -> if is_local_assum decl then s :: subst' else subst')
	    [] subst (k.cl_props @ snd k.cl_context)
	  in
	  let (app, ty_constr) = instance_constructor (k,u) subst in
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
      let _ = evars := Evarutil.nf_evar_map_undefined !evars in
      let evm, nf = Evarutil.nf_evar_map_universes !evars in
      let termtype = nf termtype in
      let _ = (* Check that the type is free of evars now. *)
	Pretyping.check_evars env Evd.empty evm termtype
      in
      let term = Option.map nf term in
	if not (Evd.has_undefined evm) && not (Option.is_empty term) then
	  declare_instance_constant k pri global imps ?hook id pl
            poly evm (Option.get term) termtype
	else if Flags.is_program_mode () || refine || Option.is_empty term then begin
	  let kind = Decl_kinds.Global, poly, Decl_kinds.DefinitionBody Decl_kinds.Instance in
	    if Flags.is_program_mode () then
	      let hook vis gr _ =
		let cst = match gr with ConstRef kn -> kn | _ -> assert false in
		  Impargs.declare_manual_implicits false gr ~enriching:false [imps];
		  Typeclasses.declare_instance pri (not global) (ConstRef cst)
	      in
	      let obls, constr, typ =
		match term with 
		| Some t -> 
		  let obls, _, constr, typ = 
		    Obligations.eterm_obligations env id evm 0 t termtype
		  in obls, Some constr, typ
		| None -> [||], None, termtype
	      in
              let hook = Lemmas.mk_hook hook in
	      let ctx = Evd.evar_universe_context evm in
		ignore (Obligations.add_definition id ?term:constr
 			?pl typ ctx ~kind:(Global,poly,Instance) ~hook obls);
		id
	    else
	      (Flags.silently 
	       (fun () ->
                  (* spiwack: it is hard to reorder the actions to do
                     the pretyping after the proof has opened. As a
                     consequence, we use the low-level primitives to code
                     the refinement manually.*)
		let gls = List.rev (Evd.future_goals evm) in
                let evm = Evd.reset_future_goals evm in
                Lemmas.start_proof id kind evm termtype
		(Lemmas.mk_hook
                  (fun _ -> instance_hook k pri global imps ?hook));
                 (* spiwack: I don't know what to do with the status here. *)
		if not (Option.is_empty term) then
                  let init_refine =
                    Tacticals.New.tclTHENLIST [
                      Refine.refine { run = fun evm -> Sigma (Option.get term, evm, Sigma.refl) };
                      Proofview.Unsafe.tclNEWGOALS gls;
                      Tactics.New.reduce_after_refine;
                    ]
                  in
		  ignore (Pfedit.by init_refine)
		else if Flags.is_auto_intros () then
		  ignore (Pfedit.by (Tacticals.New.tclDO len Tactics.intro));
		(match tac with Some tac -> ignore (Pfedit.by tac) | None -> ())) ();
	       id)
	end
      else CErrors.error "Unsolved obligations remaining.")
	
let named_of_rel_context l =
  let acc, ctx =
    List.fold_right
      (fun decl (subst, ctx) ->
        let id = match get_name decl with Anonymous -> invalid_arg "named_of_rel_context" | Name id -> id in
	let d = match decl with
	  | LocalAssum (_,t) -> id, None, substl subst t
	  | LocalDef (_,b,t) -> id, Some (substl subst b), substl subst t in
	  (mkVar id :: subst, d :: ctx))
      l ([], [])
  in ctx

let context poly l =
  let env = Global.env() in
  let evars = ref (Evd.from_env env) in
  let _, ((env', fullctx), impls) = interp_context_evars env evars l in
  let subst = Evarutil.evd_comb0 Evarutil.nf_evars_and_universes evars in
  let fullctx = Context.Rel.map subst fullctx in
  let ce t = Pretyping.check_evars env Evd.empty !evars t in
  let () = List.iter (fun decl -> Context.Rel.Declaration.iter_constr ce decl) fullctx in
  let ctx =
    try named_of_rel_context fullctx
    with e when CErrors.noncritical e ->
      error "Anonymous variables not allowed in contexts."
  in
  let uctx = ref (Evd.universe_context_set !evars) in
  let fn status (id, b, t) =
    if Lib.is_modtype () && not (Lib.sections_are_opened ()) then
      let ctx = Univ.ContextSet.to_context !uctx in
      (* Declare the universe context once *)
      let () = uctx := Univ.ContextSet.empty in
      let decl = (ParameterEntry (None,poly,(t,ctx),None), IsAssumption Logical) in
      let cst = Declare.declare_constant ~internal:Declare.InternalTacticRequest id decl in
	match class_of_constr t with
	| Some (rels, ((tc,_), args) as _cl) ->
	    add_instance (Typeclasses.new_instance tc None false (*FIXME*)
			    poly (ConstRef cst));
            status
	    (* declare_subclasses (ConstRef cst) cl *)
	| None -> status
    else
      let test (x, _) = match x with
      | ExplByPos (_, Some id') -> Id.equal id id'
      | _ -> false
      in
      let impl = List.exists test impls in
      let decl = (Discharge, poly, Definitional) in
      let nstatus =
        pi3 (Command.declare_assumption false decl (t, !uctx) [] [] impl
          Vernacexpr.NoInline (Loc.ghost, id))
      in
      let () = uctx := Univ.ContextSet.empty in
	status && nstatus
  in List.fold_left fn true (List.rev ctx)
