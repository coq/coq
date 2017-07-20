(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module is about the low-level declaration of logical objects *)

open Pp
open CErrors
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
  | UserAutomaticRequest (* kernel action, a message is displayed *)
  | InternalTacticRequest  (* kernel action, no message is displayed *)
  | UserIndividualRequest   (* user action, a message is displayed *)

(** XML output hooks *)

let (f_xml_declare_variable, xml_declare_variable) = Hook.make ~default:ignore ()
let (f_xml_declare_constant, xml_declare_constant) = Hook.make ~default:ignore ()
let (f_xml_declare_inductive, xml_declare_inductive) = Hook.make ~default:ignore ()

let if_xml f x = if !Flags.xml_export then f x else ()

(** Declaration of section variables and local definitions *)

type section_variable_entry =
  | SectionLocalDef of Safe_typing.private_constants definition_entry
  | SectionLocalAssum of types Univ.in_universe_context_set * polymorphic * bool (** Implicit status *)

type variable_declaration = DirPath.t * section_variable_entry * logical_kind

let cache_variable ((sp,_),o) =
  match o with
  | Inl ctx -> Global.push_context_set false ctx
  | Inr (id,(p,d,mk)) ->
  (* Constr raisonne sur les noms courts *)
  if variable_exists id then
    alreadydeclared (pr_id id ++ str " already exists");

  let impl,opaq,poly,ctx = match d with (* Fails if not well-typed *)
    | SectionLocalAssum ((ty,ctx),poly,impl) ->
      let () = Global.push_named_assum ((id,ty,poly),ctx) in
      let impl = if impl then Implicit else Explicit in
	impl, true, poly, ctx
    | SectionLocalDef (de) ->
      let univs = Global.push_named_def (id,de) in
      Explicit, de.const_entry_opaque,
      de.const_entry_polymorphic, univs in
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
  if_xml (Hook.get f_xml_declare_variable) oname;
  oname


(** Declaration of constants and parameters *)

type constant_obj = {
  cst_decl : global_declaration;
  cst_hyps : Dischargedhypsmap.discharged_hyps;
  cst_kind : logical_kind;
  cst_locl : bool;
  mutable cst_exported : Safe_typing.exported_private_constant list;
  (* mutable: to avoid change the libobject API, since cache_function
   * does not return an updated object *)
  mutable cst_was_seff : bool
}

type constant_declaration = Safe_typing.private_constants constant_entry * logical_kind

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
        match Opaqueproof.get_constraints (Global.opaque_tables ()) lc with
        | Some f when Future.is_val f ->
	   Global.push_context_set false (Future.force f)
        | _ -> ()

let exists_name id =
  variable_exists id || Global.exists_objlabel (Label.of_id id)

let check_exists sp =
  let id = basename sp in
  if exists_name id then alreadydeclared (pr_id id ++ str " already exists")

let cache_constant ((sp,kn), obj) =
  let id = basename sp in
  let _,dir,_ = repr_kn kn in
  let kn' =
    if obj.cst_was_seff then begin
      obj.cst_was_seff <- false;  
      if Global.exists_objlabel (Label.of_id (basename sp))
      then constant_of_kn kn
      else CErrors.anomaly Pp.(str"Ex seff not found: " ++ Id.print(basename sp) ++ str".")
    end else
      let () = check_exists sp in
      let kn', exported = Global.add_constant dir id obj.cst_decl in
      obj.cst_exported <- exported;
      kn' in
  assert (eq_constant kn' (constant_of_kn kn));
  Nametab.push (Nametab.Until 1) sp (ConstRef (constant_of_kn kn));
  let cst = Global.lookup_constant kn' in
  add_section_constant (Declareops.constant_is_polymorphic cst) kn' cst.const_hyps;
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
  ConstantEntry
    (false, ParameterEntry (None,false,(mkProp,Univ.UContext.empty),None))

let dummy_constant cst = {
  cst_decl = dummy_constant_entry;
  cst_hyps = [];
  cst_kind = cst.cst_kind;
  cst_locl = cst.cst_locl;
  cst_exported = [];
  cst_was_seff = cst.cst_was_seff;
}

let classify_constant cst = Substitute (dummy_constant cst)

let (inConstant, outConstant : (constant_obj -> obj) * (obj -> constant_obj)) =
  declare_object_full { (default_object "CONSTANT") with
    cache_function = cache_constant;
    load_function = load_constant;
    open_function = open_constant;
    classify_function = classify_constant;
    subst_function = ident_subst_function;
    discharge_function = discharge_constant }

let declare_scheme = ref (fun _ _ -> assert false)
let set_declare_scheme f = declare_scheme := f

let declare_constant_common id cst =
  let update_tables c =
(*  Printf.eprintf "tables: %s\n%!" (Names.Constant.to_string c); *)
    declare_constant_implicits c;
    Heads.declare_head (EvalConstRef c);
    Notation.declare_ref_arguments_scope (ConstRef c) in
  let o = inConstant cst in
  let _, kn as oname = add_leaf id o in
  List.iter (fun (c,ce,role) ->
      (* handling of private_constants just exported *)
      let o = inConstant {
        cst_decl = ConstantEntry (false, ce);
        cst_hyps = [] ;
        cst_kind = IsProof Theorem;
        cst_locl = false;
        cst_exported = [];
        cst_was_seff = true; } in
      let id = Label.to_id (pi3 (Constant.repr3 c)) in
      ignore(add_leaf id o);
      update_tables c;
      let () = if_xml (Hook.get f_xml_declare_constant) (InternalTacticRequest, c) in
      match role with
      | Safe_typing.Subproof -> ()
      | Safe_typing.Schema (ind, kind) -> !declare_scheme kind [|ind,c|])
    (outConstant o).cst_exported;
  pull_to_head oname;
  let c = Global.constant_of_delta_kn kn in
  update_tables c;
  c

let definition_entry ?fix_exn ?(opaque=false) ?(inline=false) ?types
    ?(poly=false) ?(univs=Univ.UContext.empty) ?(eff=Safe_typing.empty_private_constants) body =
  { const_entry_body = Future.from_val ?fix_exn ((body,Univ.ContextSet.empty), eff);
    const_entry_secctx = None;
    const_entry_type = types;
    const_entry_polymorphic = poly;
    const_entry_universes = univs;
    const_entry_opaque = opaque;
    const_entry_feedback = None;
    const_entry_inline_code = inline}

let declare_constant ?(internal = UserIndividualRequest) ?(local = false) id ?(export_seff=false) (cd, kind) =
  let export = (* We deal with side effects *)
    match cd with
    | DefinitionEntry de when
        export_seff ||
        not de.const_entry_opaque ||
        de.const_entry_polymorphic ->
          let bo = de.const_entry_body in
          let _, seff = Future.force bo in
          Safe_typing.empty_private_constants <> seff
    | _ -> false
  in
  let cst = {
    cst_decl = ConstantEntry (export,cd);
    cst_hyps = [] ;
    cst_kind = kind;
    cst_locl = local;
    cst_exported = [];
    cst_was_seff = false;
  } in
  let kn = declare_constant_common id cst in
  let () = if_xml (Hook.get f_xml_declare_constant) (internal, kn) in
  kn

let declare_definition ?(internal=UserIndividualRequest)
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
  add_section_kn (Declareops.inductive_is_polymorphic mind) kn' mind.mind_hyps;
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
  mind_entry_universes = Monomorphic_ind_entry Univ.UContext.empty;
  mind_entry_private = None;
})

(* reinfer subtyping constraints for inductive after section is dischared. *)
let infer_inductive_subtyping (pth, mind_ent) =
  match mind_ent.mind_entry_universes with
  | Monomorphic_ind_entry _ | Polymorphic_ind_entry _ ->
    (pth, mind_ent)
  | Cumulative_ind_entry cumi ->
    begin
      let env = Global.env () in
      let env' =
        Environ.push_context
          (Univ.CumulativityInfo.univ_context cumi) env
      in
      (* let (env'', typed_params) = Typeops.infer_local_decls env' (mind_ent.mind_entry_params) in *)
      let evd = Evd.from_env env' in
        (pth, Inductiveops.infer_inductive_subtyping env' evd mind_ent)
    end

type inductive_obj = Dischargedhypsmap.discharged_hyps * mutual_inductive_entry

let inInductive : inductive_obj -> obj =
  declare_object {(default_object "INDUCTIVE") with
    cache_function = cache_inductive;
    load_function = load_inductive;
    open_function = open_inductive;
    classify_function = (fun a -> Substitute (dummy_inductive_entry a));
    subst_function = ident_subst_function;
    discharge_function = discharge_inductive;
    rebuild_function = infer_inductive_subtyping }

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
	  assert(eq_constant kn kn')) kns; true,true
    | Some None -> true,false
    | None -> false,false

(* for initial declaration *)
let declare_mind mie =
  let id = match mie.mind_entry_inds with
    | ind::_ -> ind.mind_entry_typename
    | [] -> anomaly (Pp.str "cannot declare an empty list of inductives.") in
  let (sp,kn as oname) = add_leaf id (inInductive ([],mie)) in
  let mind = Global.mind_of_delta_kn kn in
  let isrecord,isprim = declare_projections mind in
  declare_mib_implicits mind;
  declare_inductive_argument_scopes mind mie;
  if_xml (Hook.get f_xml_declare_inductive) (isrecord,oname);
  oname, isprim

(* Declaration messages *)

let pr_rank i = pr_nth (i+1)

let fixpoint_message indexes l =
  Flags.if_verbose Feedback.msg_info (match l with
  | [] -> anomaly (Pp.str "no recursive definition.")
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
  Flags.if_verbose Feedback.msg_info (match l with
  | [] -> anomaly (Pp.str "No corecursive definition.")
  | [id] -> pr_id id ++ str " is corecursively defined"
  | l -> hov 0 (prlist_with_sep pr_comma pr_id l ++
                    spc () ++ str "are corecursively defined"))

let recursive_message isfix i l =
  (if isfix then fixpoint_message i else cofixpoint_message) l

let definition_message id =
  Flags.if_verbose Feedback.msg_info (pr_id id ++ str " is defined")

let assumption_message id =
  (* Changing "assumed" to "declared", "assuming" referring more to
  the type of the object than to the name of the object (see
  discussion on coqdev: "Chapter 4 of the Reference Manual", 8/10/2015) *)
  Flags.if_verbose Feedback.msg_info (pr_id id ++ str " is declared")

(** Global universe names, in a different summary *)

type universe_context_decl = polymorphic * Univ.universe_context_set

let cache_universe_context (p, ctx) =
  Global.push_context_set p ctx;
  if p then Lib.add_section_context ctx

let input_universe_context : universe_context_decl -> Libobject.obj =
  declare_object
    { (default_object "Global universe context state") with
      cache_function = (fun (na, pi) -> cache_universe_context pi);
      load_function = (fun _ (_, pi) -> cache_universe_context pi);
      discharge_function = (fun (_, (p, _ as x)) -> if p then None else Some x);
      classify_function = (fun a -> Keep a) }

let declare_universe_context poly ctx =
  Lib.add_anonymous_leaf (input_universe_context (poly, ctx))

(* Discharged or not *)
type universe_decl = polymorphic * (Id.t * Univ.universe_level) list

let cache_universes (p, l) =
  let glob = Global.global_universe_names () in
  let glob', ctx =
    List.fold_left (fun ((idl,lid),ctx) (id, lev) ->
        ((Idmap.add id (p, lev) idl,
          Univ.LMap.add lev id lid),
         Univ.ContextSet.add_universe lev ctx))
      (glob, Univ.ContextSet.empty) l
  in
  cache_universe_context (p, ctx);
  Global.set_global_universe_names glob'

let input_universes : universe_decl -> Libobject.obj =
  declare_object
    { (default_object "Global universe name state") with
      cache_function = (fun (na, pi) -> cache_universes pi);
      load_function = (fun _ (_, pi) -> cache_universes pi);
      discharge_function = (fun (_, (p, _ as x)) -> if p then None else Some x);
      classify_function = (fun a -> Keep a) }

let do_universe poly l =
  let in_section = Lib.sections_are_opened () in
  let () =
    if poly && not in_section then
      user_err ~hdr:"Constraint"
                   (str"Cannot declare polymorphic universes outside sections")
  in
  let l =
    List.map (fun (l, id) ->
	      let lev = Universes.new_univ_level (Global.current_dirpath ()) in
	      (id, lev)) l
  in
    Lib.add_anonymous_leaf (input_universes (poly, l))

type constraint_decl = polymorphic * Univ.constraints

let cache_constraints (na, (p, c)) =
  let ctx =
    Univ.ContextSet.add_constraints c
      Univ.ContextSet.empty (* No declared universes here, just constraints *)
  in cache_universe_context (p,ctx)

let discharge_constraints (_, (p, c as a)) =
  if p then None else Some a

let input_constraints : constraint_decl -> Libobject.obj =
  let open Libobject in
    declare_object
    { (default_object "Global universe constraints") with
      cache_function = cache_constraints;
      load_function = (fun _ -> cache_constraints);
      discharge_function = discharge_constraints;
      classify_function = (fun a -> Keep a) }

let do_constraint poly l =
  let open Misctypes in
  let u_of_id x =
    match x with
    | GProp -> Loc.tag (false, Univ.Level.prop)
    | GSet  -> Loc.tag (false, Univ.Level.set)
    | GType None | GType (Some (_, Anonymous)) ->
       user_err ~hdr:"Constraint"
                     (str "Cannot declare constraints on anonymous universes")
    | GType (Some (loc, Name id)) ->
       let names, _ = Global.global_universe_names () in
       try loc, Idmap.find id names
       with Not_found ->
         user_err ?loc ~hdr:"Constraint" (str "Undeclared universe " ++ pr_id id)
  in
  let in_section = Lib.sections_are_opened () in
  let () =
    if poly && not in_section then
      user_err ~hdr:"Constraint"
                    (str"Cannot declare polymorphic constraints outside sections")
  in
  let check_poly ?loc p loc' p' =
    if poly then ()
    else if p || p' then
      let loc = if p then loc else loc' in
      user_err ?loc ~hdr:"Constraint"
                    (str "Cannot declare a global constraint on " ++
                    str "a polymorphic universe, use "
                    ++ str "Polymorphic Constraint instead")
  in
  let constraints = List.fold_left (fun acc (l, d, r) ->
     let ploc, (p, lu) = u_of_id l and rloc, (p', ru) = u_of_id r in
     check_poly ?loc:ploc p rloc p';
     Univ.Constraint.add (lu, d, ru) acc)
    Univ.Constraint.empty l
  in
    Lib.add_anonymous_leaf (input_constraints (poly, constraints))
