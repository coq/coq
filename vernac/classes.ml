(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Names
open EConstr
open Nametab
open CErrors
open Util
open Typeclasses_errors
open Typeclasses
open Libnames
open Globnames
open Constrintern
open Constrexpr
open Context.Rel.Declaration

module RelDecl = Context.Rel.Declaration
(*i*)

open Decl_kinds
open Entries

let refine_instance = ref true

let _ = Goptions.declare_bool_option {
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
    (fun inst path local info poly ->
     let inst' = match inst with IsConstr c -> Hints.IsConstr (EConstr.of_constr c, Univ.ContextSet.empty)
       | IsGlobal gr -> Hints.IsGlobRef gr
     in
     let info =
       let open Vernacexpr in
       { info with hint_pattern =
		   Option.map
		     (Constrintern.intern_constr_pattern (Global.env()))
		     info.hint_pattern } in
     Flags.silently (fun () ->
	Hints.add_hints local [typeclasses_db]
	  (Hints.HintsResolveEntry
	     [info, poly, false, Hints.PathHints path, inst'])) ());
  Hook.set Typeclasses.set_typeclass_transparency_hook set_typeclass_transparency;
  Hook.set Typeclasses.classes_transparent_state_hook
    (fun () -> Hints.Hint_db.transparent_state (Hints.searchtable_map typeclasses_db))

(** TODO: add subinstances *)
let existing_instance glob g info =
  let c = global g in
  let info = Option.default Hints.empty_hint_info info in
  let instance, _ = Global.type_of_global_in_context (Global.env ()) c in
  let _, r = Term.decompose_prod_assum instance in
    match class_of_constr Evd.empty (EConstr.of_constr r) with
      | Some (_, ((tc,u), _)) -> add_instance (new_instance tc info glob
  (*FIXME*) (Flags.use_polymorphic_flag ()) c)
      | None -> user_err ?loc:(loc_of_reference g)
                         ~hdr:"declare_instance"
                         (Pp.str "Constant does not build instances of a declared type class.")

let mismatched_params env n m = mismatched_ctx_inst env Parameters n m
let mismatched_props env n m = mismatched_ctx_inst env Properties n m

(* Declare everything in the parameters as implicit, and the class instance as well *)

let type_ctx_instance env sigma ctx inst subst =
  let open Vars in
  let rec aux (sigma, subst, instctx) l = function
    decl :: ctx ->
      let t' = substl subst (RelDecl.get_type decl) in
      let (sigma, c'), l =
	match decl with
        | LocalAssum _ -> interp_casted_constr_evars env sigma (List.hd l) t', List.tl l
        | LocalDef (_,b,_) -> (sigma, substl subst b), l
      in
      let d = RelDecl.get_name decl, Some c', t' in
        aux (sigma, c' :: subst, d :: instctx) l ctx
    | [] -> sigma, subst
  in aux (sigma, subst, []) inst (List.rev ctx)

let id_of_class cl =
  match cl.cl_impl with
    | ConstRef kn -> let _,_,l = Constant.repr3 kn in Label.to_id l
    | IndRef (kn,i) ->
	let mip = (Environ.lookup_mind kn (Global.env ())).Declarations.mind_packets in
	  mip.(0).Declarations.mind_typename
    | _ -> assert false

open Pp

let instance_hook k info global imps ?hook cst =
  Impargs.maybe_declare_manual_implicits false cst ~enriching:false imps;
  Typeclasses.declare_instance (Some info) (not global) cst;
  (match hook with Some h -> h cst | None -> ())

let declare_instance_constant k info global imps ?hook id decl poly sigma term termtype =
  let kind = IsDefinition Instance in
  let sigma =
    let env = Global.env () in
    let levels = Univ.LSet.union (Univops.universes_of_constr env termtype)
                                 (Univops.universes_of_constr env term) in
    Evd.restrict_universe_context sigma levels
  in
  let uctx = Evd.check_univ_decl ~poly sigma decl in
  let entry = 
    Declare.definition_entry ~types:termtype ~univs:uctx term
  in
  let cdecl = (DefinitionEntry entry, kind) in
  let kn = Declare.declare_constant id cdecl in
    Declare.definition_message id;
    Declare.declare_univ_binders (ConstRef kn) (Evd.universe_binders sigma);
    instance_hook k info global imps ?hook (ConstRef kn);
    id

let get_default_generalize_instance =
  let ref = ref true in
  let open Goptions in
  let _ = declare_bool_option
           { optdepr  = false;
             optname  = "generalize variables in the type of an Instance";
             optkey   = ["Typeclasses";"Default";"Generalize";"Instance";"Variables"];
             optread  = (fun () -> !ref);
             optwrite = (fun b -> ref := b); }
  in
  fun () -> if !ref then Explicit else Implicit

let new_instance ?(abstract=false) ?(global=false) ?(refine= !refine_instance)
  ~program_mode poly ctx (instid, bk, cl) props ?(generalize=true)
  ?(tac:unit Proofview.tactic option) ?hook pri =
  let env = Global.env() in
  let bk = Option.default (get_default_generalize_instance ()) bk in
  let ((loc, instid), pl) = instid in
  let sigma, decl = Univdecls.interp_univ_decl_opt env pl in
  let tclass, ids =
    match bk with
    | Decl_kinds.Implicit ->
	Implicit_quantifiers.implicit_application Id.Set.empty ~allow_partial:false
	  (fun avoid (clname, _) ->
	    match clname with
            | Some cl ->
		let t = CAst.make @@ CHole (None, Misctypes.IntroAnonymous, None) in
		  t, avoid
	    | None -> failwith ("new instance: under-applied typeclass"))
	  cl
    | Explicit -> cl, Id.Set.empty
  in
  let tclass = 
    if generalize then CAst.make @@ CGeneralization (Implicit, Some AbsPi, tclass) 
    else tclass 
  in
  let sigma, k, u, cty, ctx', ctx, len, imps, subst =
    let sigma, (impls, ((env', ctx), imps)) = interp_context_evars env sigma ctx in
    let sigma, (c', imps') = interp_type_evars_impls ~impls env' sigma tclass in
    let len = List.length ctx in
    let imps = imps @ Impargs.lift_implicits len imps' in
    let ctx', c = decompose_prod_assum sigma c' in
    let ctx'' = ctx' @ ctx in
    let (k, u), args = Typeclasses.dest_class_app (push_rel_context ctx'' env) sigma c in
    let u_s = EInstance.kind sigma u in
    let cl = Typeclasses.typeclass_univ_instance (k, u_s) in
    let args = List.map of_constr args in
    let cl_context = List.map (Termops.map_rel_decl of_constr) (snd cl.cl_context) in
    let _, args =
      List.fold_right (fun decl (args, args') ->
	match decl with
	| LocalAssum _ -> (List.tl args, List.hd args :: args')
        | LocalDef (_,b,_) -> (args, Vars.substl args' b :: args'))
        cl_context (args, [])
    in
      sigma, cl, u, c', ctx', ctx, len, imps, args
  in
  let id =
    match instid with
	Name id ->
	  let sp = Lib.make_path id in
	    if Nametab.exists_cci sp then
	      user_err ~hdr:"new_instance" (Id.print id ++ Pp.str " already exists.");
	    id
      | Anonymous ->
	  let i = Nameops.add_suffix (id_of_class k) "_instance_0" in
	    Namegen.next_global_ident_away i (Termops.vars_of_env env)
  in
  let env' = push_rel_context ctx env in
  let sigma = Evarutil.nf_evar_map sigma in
  let sigma = resolve_typeclasses ~filter:Typeclasses.all_evars ~fail:true env sigma in
    if abstract then
      begin
	let subst = List.fold_left2
	  (fun subst' s decl -> if is_local_assum decl then s :: subst' else subst')
	  [] subst (snd k.cl_context)
	in
	let (_, ty_constr) = instance_constructor (k,u) subst in
        let termtype = it_mkProd_or_LetIn ty_constr (ctx' @ ctx) in
        let sigma,_ = Evarutil.nf_evars_and_universes sigma in
        Pretyping.check_evars env Evd.empty sigma termtype;
        let univs = Evd.check_univ_decl ~poly sigma decl in
        let termtype = to_constr sigma termtype in
        let cst = Declare.declare_constant ~internal:Declare.InternalTacticRequest id
          (ParameterEntry
            (None,(termtype,univs),None), Decl_kinds.IsAssumption Decl_kinds.Logical)
        in
          Declare.declare_univ_binders (ConstRef cst) (Evd.universe_binders sigma);
          instance_hook k pri global imps ?hook (ConstRef cst); id
      end
    else (
      let props =
	match props with
	| Some (true, { CAst.v = CRecord fs }) ->
	    if List.length fs > List.length k.cl_props then
	      mismatched_props env' (List.map snd fs) k.cl_props;
	    Some (Inl fs)
	| Some (_, t) -> Some (Inr t)
	| None -> 
            if program_mode then Some (Inl [])
	    else None
      in
      let subst, sigma =
	match props with
        | None ->
          (if List.is_empty k.cl_props then Some (Inl subst) else None), sigma
	| Some (Inr term) ->
            let sigma, c = interp_casted_constr_evars env' sigma term cty in
            Some (Inr (c, subst)), sigma
	| Some (Inl props) ->
	    let get_id =
	      function
		| Ident id' -> id'
		| Qualid (loc,id') -> (Loc.tag ?loc @@ snd (repr_qualid id'))
	    in
	    let props, rest =
	      List.fold_left
		(fun (props, rest) decl ->
		  if is_local_assum decl then
		    try
		      let is_id (id', _) = match RelDecl.get_name decl, get_id id' with
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
					Option.iter (fun x -> Dumpglob.add_glob ?loc (ConstRef x)) x)
			   k.cl_projs;
			 c :: props, rest'
		     with Not_found ->
		       ((CAst.make @@ CHole (None(* Some Evar_kinds.GoalEvar *), Misctypes.IntroAnonymous, None)) :: props), rest
		   else props, rest)
		([], props) k.cl_props
	    in
              match rest with
              | (n, _) :: _ ->
		unbound_method env' k.cl_impl (get_id n)
              | _ ->
                let kcl_props = List.map (Termops.map_rel_decl of_constr) k.cl_props in
                let sigma, res = type_ctx_instance (push_rel_context ctx' env') sigma kcl_props props subst in
                Some (Inl res), sigma
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
          let term = it_mkLambda_or_LetIn (Option.get app) (ctx' @ ctx) in
	    Some term, termtype
	| Some (Inr (def, subst)) ->
	  let termtype = it_mkProd_or_LetIn cty ctx in
          let term = it_mkLambda_or_LetIn def ctx in
	    Some term, termtype
      in
      let sigma = Evarutil.nf_evar_map sigma in
      let sigma = Typeclasses.resolve_typeclasses ~filter:Typeclasses.no_goals_or_obligations ~fail:true env sigma in
      (* Try resolving fields that are typeclasses automatically. *)
      let sigma = Typeclasses.resolve_typeclasses ~filter:Typeclasses.all_evars ~fail:false env sigma in
      let sigma = Evarutil.nf_evar_map_undefined sigma in
      (* Beware of this step, it is required as to minimize universes. *)
      let sigma, _nf = Evarutil.nf_evar_map_universes sigma in
      (* Check that the type is free of evars now. *)
      Pretyping.check_evars env Evd.empty sigma termtype;
      let termtype = to_constr sigma termtype in
      let term = Option.map (to_constr sigma) term in
        if not (Evd.has_undefined sigma) && not (Option.is_empty term) then
	  declare_instance_constant k pri global imps ?hook id decl
            poly sigma (Option.get term) termtype
        else if program_mode || refine || Option.is_empty term then begin
	  let kind = Decl_kinds.Global, poly, Decl_kinds.DefinitionBody Decl_kinds.Instance in
            if program_mode then
	      let hook vis gr _ =
		let cst = match gr with ConstRef kn -> kn | _ -> assert false in
		  Impargs.declare_manual_implicits false gr ~enriching:false [imps];
		  Typeclasses.declare_instance (Some pri) (not global) (ConstRef cst)
	      in
	      let obls, constr, typ =
		match term with 
		| Some t -> 
		  let obls, _, constr, typ = 
                    Obligations.eterm_obligations env id sigma 0 t termtype
		  in obls, Some constr, typ
		| None -> [||], None, termtype
	      in
              let hook = Lemmas.mk_hook hook in
              let ctx = Evd.evar_universe_context sigma in
		ignore (Obligations.add_definition id ?term:constr
 			~univdecl:decl typ ctx ~kind:(Global,poly,Instance) ~hook obls);
		id
	    else
	      (Flags.silently 
	       (fun () ->
                  (* spiwack: it is hard to reorder the actions to do
                     the pretyping after the proof has opened. As a
                     consequence, we use the low-level primitives to code
                     the refinement manually.*)
                let gls = List.rev (Evd.future_goals sigma) in
                let sigma = Evd.reset_future_goals sigma in
                Lemmas.start_proof id ~pl:decl kind sigma (EConstr.of_constr termtype)
		(Lemmas.mk_hook
                  (fun _ -> instance_hook k pri global imps ?hook));
                 (* spiwack: I don't know what to do with the status here. *)
		if not (Option.is_empty term) then
                  let init_refine =
                    Tacticals.New.tclTHENLIST [
                      Refine.refine ~typecheck:false (fun sigma -> (sigma,EConstr.of_constr (Option.get term)));
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
      else CErrors.user_err Pp.(str "Unsolved obligations remaining."))
	
let named_of_rel_context l =
  let open Vars in
  let acc, ctx =
    List.fold_right
      (fun decl (subst, ctx) ->
        let id = match RelDecl.get_name decl with Anonymous -> invalid_arg "named_of_rel_context" | Name id -> id in
	let d = match decl with
	  | LocalAssum (_,t) -> id, None, substl subst t
	  | LocalDef (_,b,t) -> id, Some (substl subst b), substl subst t in
	  (mkVar id :: subst, d :: ctx))
      l ([], [])
  in ctx

let context poly l =
  let env = Global.env() in
  let sigma = Evd.from_env env in
  let sigma, (_, ((env', fullctx), impls)) = interp_context_evars env sigma l in
  (* Note, we must use the normalized evar from now on! *)
  let sigma,_ = Evarutil.nf_evars_and_universes sigma in
  let ce t = Pretyping.check_evars env Evd.empty sigma t in
  let () = List.iter (fun decl -> Context.Rel.Declaration.iter_constr ce decl) fullctx in
  let ctx =
    try named_of_rel_context fullctx
    with e when CErrors.noncritical e ->
      user_err Pp.(str "Anonymous variables not allowed in contexts.")
  in
  let uctx = ref (Evd.universe_context_set sigma) in
  let fn status (id, b, t) =
    let b, t = Option.map (to_constr sigma) b, to_constr sigma t in
    if Lib.is_modtype () && not (Lib.sections_are_opened ()) then
      (* Declare the universe context once *)
      let univs = if poly
        then Polymorphic_const_entry (Univ.ContextSet.to_context !uctx)
        else Monomorphic_const_entry !uctx
      in
      let () = uctx := Univ.ContextSet.empty in
      let decl = match b with
      | None ->
        (ParameterEntry (None,(t,univs),None), IsAssumption Logical)
      | Some b ->
        let entry = Declare.definition_entry ~univs ~types:t b in
        (DefinitionEntry entry, IsAssumption Logical)
      in
      let cst = Declare.declare_constant ~internal:Declare.InternalTacticRequest id decl in
        match class_of_constr sigma (of_constr t) with
	| Some (rels, ((tc,_), args) as _cl) ->
	    add_instance (Typeclasses.new_instance tc Hints.empty_hint_info false (*FIXME*)
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
      let univs = if poly
        then Polymorphic_const_entry (Univ.ContextSet.to_context !uctx)
        else Monomorphic_const_entry !uctx
      in
      let nstatus = match b with
      | None ->
        pi3 (ComAssumption.declare_assumption false decl (t, univs) Universes.empty_binders [] impl
          Vernacexpr.NoInline (Loc.tag id))
      | Some b ->
        let decl = (Discharge, poly, Definition) in
        let entry = Declare.definition_entry ~univs ~types:t b in
        let hook = Lemmas.mk_hook (fun _ gr -> gr) in
        let _ = DeclareDef.declare_definition id decl entry Universes.empty_binders [] hook in
        Lib.sections_are_opened () || Lib.is_modtype_strict ()
      in
	status && nstatus
  in 
  if Lib.sections_are_opened () then
    Declare.declare_universe_context poly !uctx;
  List.fold_left fn true (List.rev ctx)
