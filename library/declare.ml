(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module is about the low-level declaration of logical objects *)

open Pp
open Errors
open Util
open Names
open Libnames
open Globnames
open Nameops
open Term
open Declarations
open Entries
open Libobject
open Lib
open Impargs
open Safe_typing
open Cooking
open Decls
open Decl_kinds

(** flag for internal message display *)
type internal_flag = 
  | KernelVerbose (* kernel action, a message is displayed *)
  | KernelSilent  (* kernel action, no message is displayed *)
  | UserVerbose   (* user action, a message is displayed *)

(** Declaration of section variables and local definitions *)

type section_variable_entry =
  | SectionLocalDef of definition_entry
  | SectionLocalAssum of types Univ.in_universe_context_set * polymorphic * bool (** Implicit status *)

type variable_declaration = DirPath.t * section_variable_entry * logical_kind

let cache_variable ((sp,_),o) =
  match o with
  | Inl ctx -> Global.push_context_set ctx
  | Inr (id,(p,d,mk)) ->
  (* Constr raisonne sur les noms courts *)
  if variable_exists id then
    alreadydeclared (pr_id id ++ str " already exists");

  let impl,opaq,poly,ctx = match d with (* Fails if not well-typed *)
    | SectionLocalAssum ((ty,ctx),poly,impl) ->
      let () = Global.push_named_assum ((id,ty),ctx) in
      let impl = if impl then Implicit else Explicit in
	impl, true, poly, ctx
    | SectionLocalDef (de) ->
      let () = Global.push_named_def (id,de) in
        Explicit, de.const_entry_opaque, de.const_entry_polymorphic, 
	(Univ.ContextSet.of_context de.const_entry_universes) in
  Nametab.push (Nametab.Until 1) (restrict_path 0 sp) (VarRef id);
  add_section_variable id impl poly ctx;
  Dischargedhypsmap.set_discharged_hyps sp [];
  add_variable_data id (p,opaq,ctx,poly,mk)

let discharge_variable (_,o) = match o with
  | Inr (id,_) -> 
    if variable_polymorphic id then None
    else Some (Inl (variable_context id))
  | Inl _ -> Some o

type variable_obj =
    (Univ.ContextSet.t, Id.t * variable_declaration) union

let inVariable : variable_obj -> obj =
  declare_object { (default_object "VARIABLE") with
    cache_function = cache_variable;
    discharge_function = discharge_variable;
    classify_function = (fun _ -> Dispose) }

(* for initial declaration *)
let declare_variable id obj =
  let oname = add_leaf id (inVariable (Inr (id,obj))) in
  declare_var_implicits id;
  Notation.declare_ref_arguments_scope (VarRef id);
  Heads.declare_head (EvalVarRef id);
  oname


(** Declaration of constants and parameters *)

type constant_obj = {
  cst_decl : global_declaration;
  cst_hyps : Dischargedhypsmap.discharged_hyps;
  cst_kind : logical_kind;
  cst_locl : bool;
}

type constant_declaration = constant_entry * logical_kind

(* At load-time, the segment starting from the module name to the discharge *)
(* section (if Remark or Fact) is needed to access a construction *)
let load_constant i ((sp,kn), obj) =
  if Nametab.exists_cci sp then
    alreadydeclared (pr_id (basename sp) ++ str " already exists");
  let con = Global.constant_of_delta_kn kn in
  Nametab.push (Nametab.Until i) sp (ConstRef con);
  add_constant_kind con obj.cst_kind

(* Opening means making the name without its module qualification available *)
let open_constant i ((sp,kn), obj) =
  (** Never open a local definition *)
  if obj.cst_locl then ()
  else
    let con = Global.constant_of_delta_kn kn in
    Nametab.push (Nametab.Exactly i) sp (ConstRef con);
    match (Global.lookup_constant con).const_body with
    | (Def _ | Undef _) -> ()
    | OpaqueDef lc ->
        match Opaqueproof.get_constraints (Global.opaque_tables ())lc with
        | Some f when Future.is_val f -> Global.push_context_set (Future.force f)
        | _ -> ()

let exists_name id =
  variable_exists id || Global.exists_objlabel (Label.of_id id)

let check_exists sp =
  let id = basename sp in
  if exists_name id then alreadydeclared (pr_id id ++ str " already exists")

let cache_constant ((sp,kn), obj) =
  let id = basename sp in
  let _,dir,_ = repr_kn kn in
  let () = check_exists sp in
  let kn' = Global.add_constant dir id obj.cst_decl in
  assert (eq_constant kn' (constant_of_kn kn));
  Nametab.push (Nametab.Until 1) sp (ConstRef (constant_of_kn kn));
  let cst = Global.lookup_constant kn' in
  add_section_constant (cst.const_proj <> None) kn' cst.const_hyps;
  Dischargedhypsmap.set_discharged_hyps sp obj.cst_hyps;
  add_constant_kind (constant_of_kn kn) obj.cst_kind

let discharged_hyps kn sechyps =
  let (_,dir,_) = repr_kn kn in
  let args = Array.to_list (instance_from_variable_context sechyps) in
  List.rev_map (Libnames.make_path dir) args

let discharge_constant ((sp, kn), obj) =
  let con = constant_of_kn kn in
  let from = Global.lookup_constant con in
  let modlist = replacement_context () in
  let hyps,subst,uctx = section_segment_of_constant con in
  let new_hyps = (discharged_hyps kn hyps) @ obj.cst_hyps in
  let abstract = (named_of_variable_context hyps, subst, uctx) in
  let new_decl = GlobalRecipe{ from; info = { Opaqueproof.modlist; abstract}} in
  Some { obj with cst_hyps = new_hyps; cst_decl = new_decl; }

(* Hack to reduce the size of .vo: we keep only what load/open needs *)
let dummy_constant_entry = 
  ConstantEntry (ParameterEntry (None,false,(mkProp,Univ.UContext.empty),None))

let dummy_constant cst = {
  cst_decl = dummy_constant_entry;
  cst_hyps = [];
  cst_kind = cst.cst_kind;
  cst_locl = cst.cst_locl;
}

let classify_constant cst = Substitute (dummy_constant cst)

let inConstant : constant_obj -> obj =
  declare_object { (default_object "CONSTANT") with
    cache_function = cache_constant;
    load_function = load_constant;
    open_function = open_constant;
    classify_function = classify_constant;
    subst_function = ident_subst_function;
    discharge_function = discharge_constant }

let declare_constant_common id cst =
  let (sp,kn) = add_leaf id (inConstant cst) in
  let c = Global.constant_of_delta_kn kn in
  declare_constant_implicits c;
  Heads.declare_head (EvalConstRef c);
  Notation.declare_ref_arguments_scope (ConstRef c);
  c

let definition_entry ?(opaque=false) ?(inline=false) ?types 
    ?(poly=false) ?(univs=Univ.UContext.empty) ?(eff=Declareops.no_seff) body =
  { const_entry_body = Future.from_val ((body,Univ.ContextSet.empty), eff);
    const_entry_secctx = None;
    const_entry_type = types;
    const_entry_polymorphic = poly;
    const_entry_universes = univs;
    const_entry_opaque = opaque;
    const_entry_feedback = None;
    const_entry_inline_code = inline}

let declare_scheme = ref (fun _ _ -> assert false)
let set_declare_scheme f = declare_scheme := f
let declare_sideff env fix_exn se =
  let cbl, scheme = match se with
    | SEsubproof (c, cb, pt) -> [c, cb, pt], None
    | SEscheme (cbl, k) ->
        List.map (fun (_,c,cb,pt) -> c,cb,pt) cbl, Some (cbl,k) in
  let id_of c = Names.Label.to_id (Names.Constant.label c) in
  let pt_opaque_of cb pt =
    match cb, pt with
    | { const_body = Def sc }, _ -> (Mod_subst.force_constr sc, Univ.ContextSet.empty), false
    | { const_body = OpaqueDef _ }, `Opaque(pt,univ) -> (pt, univ), true
    | _ -> assert false
  in
  let ty_of cb =
    match cb.Declarations.const_type with
    | Declarations.RegularArity t -> Some t 
    | Declarations.TemplateArity _ -> None in
  let cst_of cb pt =
    let pt, opaque = pt_opaque_of cb pt in
    let univs, subst = 
      if cb.const_polymorphic then
	let univs = Univ.instantiate_univ_context cb.const_universes in
	  univs, Vars.subst_instance_constr (Univ.UContext.instance univs)
      else cb.const_universes, fun x -> x
    in
    let pt = (subst (fst pt), snd pt) in
    let ty = Option.map subst (ty_of cb) in
    { cst_decl = ConstantEntry (DefinitionEntry {
        const_entry_body = Future.from_here ~fix_exn (pt, Declareops.no_seff);
        const_entry_secctx = Some cb.Declarations.const_hyps;
        const_entry_type = ty;
        const_entry_opaque = opaque;
        const_entry_inline_code = false;
        const_entry_feedback = None;
	const_entry_polymorphic = cb.const_polymorphic;
	const_entry_universes = univs;
    });
    cst_hyps = [] ;
    cst_kind =  Decl_kinds.IsDefinition Decl_kinds.Definition;
    cst_locl = true;
  } in
  let exists c =
    try ignore(Environ.lookup_constant c env); true
    with Not_found -> false in 
  let knl =
    CList.map_filter (fun (c,cb,pt) ->
      if exists c then None
      else Some (c,declare_constant_common (id_of c) (cst_of cb pt))) cbl in
  match scheme with
  | None -> ()
  | Some (inds_consts,kind) ->
      !declare_scheme kind (Array.of_list
         (List.map (fun (c,kn) ->
             CList.find_map (fun (x,c',_,_) ->
               if Constant.equal c c' then Some (x,kn) else None) inds_consts)
           knl))

let declare_constant ?(internal = UserVerbose) ?(local = false) id (cd, kind) =
  let cd = (* We deal with side effects of non-opaque constants *)
    match cd with
    | Entries.DefinitionEntry ({
      const_entry_opaque = false; const_entry_body = bo } as de)
    | Entries.DefinitionEntry ({
      const_entry_polymorphic = true; const_entry_body = bo } as de)
      ->
        let _, seff = Future.force bo in
        if Declareops.side_effects_is_empty seff then cd
        else begin
          let seff = Declareops.uniquize_side_effects seff in
          Declareops.iter_side_effects
            (declare_sideff (Global.env ()) (Future.fix_exn_of bo)) seff;
          Entries.DefinitionEntry { de with
            const_entry_body = Future.chain ~pure:true bo (fun (pt, _) ->
              pt, Declareops.no_seff) }
        end
    | _ -> cd
  in
  let cst = {
    cst_decl = ConstantEntry cd;
    cst_hyps = [] ;
    cst_kind = kind;
    cst_locl = local;
  } in
  let kn = declare_constant_common id cst in
  kn

let declare_definition ?(internal=UserVerbose) 
  ?(opaque=false) ?(kind=Decl_kinds.Definition) ?(local = false)
  ?(poly=false) id ?types (body,ctx) =
  let cb = 
    definition_entry ?types ~poly ~univs:(Univ.ContextSet.to_context ctx) ~opaque body
  in
    declare_constant ~internal ~local id
      (Entries.DefinitionEntry cb, Decl_kinds.IsDefinition kind)

(** Declaration of inductive blocks *)

let declare_inductive_argument_scopes kn mie =
  List.iteri (fun i {mind_entry_consnames=lc} ->
    Notation.declare_ref_arguments_scope (IndRef (kn,i));
    for j=1 to List.length lc do
      Notation.declare_ref_arguments_scope (ConstructRef ((kn,i),j));
    done) mie.mind_entry_inds

let inductive_names sp kn mie =
  let (dp,_) = repr_path sp in
  let kn = Global.mind_of_delta_kn kn in
  let names, _ =
    List.fold_left
      (fun (names, n) ind ->
	 let ind_p = (kn,n) in
	 let names, _ =
	   List.fold_left
	     (fun (names, p) l ->
		let sp =
		  Libnames.make_path dp l
		in
		  ((sp, ConstructRef (ind_p,p)) :: names, p+1))
	     (names, 1) ind.mind_entry_consnames in
	 let sp = Libnames.make_path dp ind.mind_entry_typename
	 in
	   ((sp, IndRef ind_p) :: names, n+1))
      ([], 0) mie.mind_entry_inds
  in names

let load_inductive i ((sp,kn),(_,mie)) =
  let names = inductive_names sp kn mie in
  List.iter (fun (sp, ref) -> Nametab.push (Nametab.Until i) sp ref ) names

let open_inductive i ((sp,kn),(_,mie)) =
  let names = inductive_names sp kn mie in
  List.iter (fun (sp, ref) -> Nametab.push (Nametab.Exactly i) sp ref) names

let cache_inductive ((sp,kn),(dhyps,mie)) =
  let names = inductive_names sp kn mie in
  List.iter check_exists (List.map fst names);
  let id = basename sp in
  let _,dir,_ = repr_kn kn in
  let kn' = Global.add_mind dir id mie in
  assert (eq_mind kn' (mind_of_kn kn));
  let mind = Global.lookup_mind kn' in
  add_section_kn kn' mind.mind_hyps;
  Dischargedhypsmap.set_discharged_hyps sp dhyps;
  List.iter (fun (sp, ref) -> Nametab.push (Nametab.Until 1) sp ref) names

let discharge_inductive ((sp,kn),(dhyps,mie)) =
  let mind = Global.mind_of_delta_kn kn in
  let mie = Global.lookup_mind mind in
  let repl = replacement_context () in
  let sechyps,usubst,uctx = section_segment_of_mutual_inductive mind in
  Some (discharged_hyps kn sechyps,
        Discharge.process_inductive (named_of_variable_context sechyps,uctx) repl mie)

let dummy_one_inductive_entry mie = {
  mind_entry_typename = mie.mind_entry_typename;
  mind_entry_arity = mkProp;
  mind_entry_template = false;
  mind_entry_consnames = mie.mind_entry_consnames;
  mind_entry_lc = []
}

(* Hack to reduce the size of .vo: we keep only what load/open needs *)
let dummy_inductive_entry (_,m) = ([],{
  mind_entry_params = [];
  mind_entry_record = None;
  mind_entry_finite = Decl_kinds.BiFinite;
  mind_entry_inds = List.map dummy_one_inductive_entry m.mind_entry_inds;
  mind_entry_polymorphic = false;
  mind_entry_universes = Univ.UContext.empty;
  mind_entry_private = None })

type inductive_obj = Dischargedhypsmap.discharged_hyps * mutual_inductive_entry

let inInductive : inductive_obj -> obj =
  declare_object {(default_object "INDUCTIVE") with
    cache_function = cache_inductive;
    load_function = load_inductive;
    open_function = open_inductive;
    classify_function = (fun a -> Substitute (dummy_inductive_entry a));
    subst_function = ident_subst_function;
    discharge_function = discharge_inductive }

let declare_projections mind =
  let spec,_ = Inductive.lookup_mind_specif (Global.env ()) (mind,0) in
    match spec.mind_record with
    | Some (Some (_, kns, pjs)) -> 
      Array.iteri (fun i kn -> 
	let id = Label.to_id (Constant.label kn) in
	let entry = {proj_entry_ind = mind; proj_entry_arg = i} in
	let kn' = declare_constant id (ProjectionEntry entry,
				       IsDefinition StructureComponent) 
	in
	  assert(eq_constant kn kn')) kns; true
    | Some None | None -> false

(* for initial declaration *)
let declare_mind mie =
  let id = match mie.mind_entry_inds with
    | ind::_ -> ind.mind_entry_typename
    | [] -> anomaly (Pp.str "cannot declare an empty list of inductives") in
  let (sp,kn as oname) = add_leaf id (inInductive ([],mie)) in
  let mind = Global.mind_of_delta_kn kn in
  let isprim = declare_projections mind in
  declare_mib_implicits mind;
  declare_inductive_argument_scopes mind mie;
  oname, isprim

(* Declaration messages *)

let pr_rank i = pr_nth (i+1)

let fixpoint_message indexes l =
  Flags.if_verbose msg_info (match l with
  | [] -> anomaly (Pp.str "no recursive definition")
  | [id] -> pr_id id ++ str " is recursively defined" ++
      (match indexes with
	 | Some [|i|] -> str " (decreasing on "++pr_rank i++str " argument)"
	 | _ -> mt ())
  | l -> hov 0 (prlist_with_sep pr_comma pr_id l ++
		  spc () ++ str "are recursively defined" ++
		  match indexes with
		    | Some a -> spc () ++ str "(decreasing respectively on " ++
			prvect_with_sep pr_comma pr_rank a ++
			str " arguments)"
		    | None -> mt ()))

let cofixpoint_message l =
  Flags.if_verbose msg_info (match l with
  | [] -> anomaly (Pp.str "No corecursive definition.")
  | [id] -> pr_id id ++ str " is corecursively defined"
  | l -> hov 0 (prlist_with_sep pr_comma pr_id l ++
                    spc () ++ str "are corecursively defined"))

let recursive_message isfix i l =
  (if isfix then fixpoint_message i else cofixpoint_message) l

let definition_message id =
  Flags.if_verbose msg_info (pr_id id ++ str " is defined")

let assumption_message id =
  Flags.if_verbose msg_info (pr_id id ++ str " is assumed")

(** Global universe names, in a different summary *)

type universe_names = 
    (Univ.universe_level Idmap.t * Id.t Univ.LMap.t)

let input_universes : universe_names -> Libobject.obj =
  let open Libobject in 
    declare_object
    { (default_object "Global universe name state") with
      cache_function = (fun (na, pi) -> Universes.set_global_universe_names pi);
      load_function = (fun _ (_, pi) -> Universes.set_global_universe_names pi);
      discharge_function = (fun (_, a) -> Some a);
      classify_function = (fun a -> Keep a) }

let do_universe l =
  let glob = Universes.global_universe_names () in
  let glob' = 
    List.fold_left (fun (idl,lid) (l, id) ->
      let lev = Universes.new_univ_level (Global.current_dirpath ()) in
	(Idmap.add id lev idl, Univ.LMap.add lev id lid))
      glob l
  in
    Lib.add_anonymous_leaf (input_universes glob')


let input_constraints : Univ.constraints -> Libobject.obj =
  let open Libobject in 
    declare_object
    { (default_object "Global universe constraints") with
      cache_function = (fun (na, c) -> Global.add_constraints c);
      load_function = (fun _ (_, c) -> Global.add_constraints c);
      discharge_function = (fun (_, a) -> Some a);
      classify_function = (fun a -> Keep a) }

let do_constraint l = 
  let u_of_id = 
    let names, _ = Universes.global_universe_names () in
      fun (loc, id) -> 
	try Idmap.find id names
	with Not_found ->
	  user_err_loc (loc, "Constraint", str "Undeclared universe " ++ pr_id id)	    
  in
  let constraints = List.fold_left (fun acc (l, d, r) ->
    let lu = u_of_id l and ru = u_of_id r in
      Univ.Constraint.add (lu, d, ru) acc)
    Univ.Constraint.empty l
  in
    Lib.add_anonymous_leaf (input_constraints constraints)
  
