(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
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

(** XML output hooks *)

let (f_xml_declare_variable, xml_declare_variable) = Hook.make ~default:ignore ()
let (f_xml_declare_constant, xml_declare_constant) = Hook.make ~default:ignore ()
let (f_xml_declare_inductive, xml_declare_inductive) = Hook.make ~default:ignore ()

let if_xml f x = if !Flags.xml_export then f x else ()

(** Declaration of section variables and local definitions *)

type section_variable_entry =
  | SectionLocalDef of definition_entry
  | SectionLocalAssum of types * bool (* Implicit status *)

type variable_declaration = DirPath.t * section_variable_entry * logical_kind

let cache_variable ((sp,_),o) =
  match o with
  | Inl cst -> Global.add_constraints cst
  | Inr (id,(p,d,mk)) ->
  (* Constr raisonne sur les noms courts *)
  if variable_exists id then
    alreadydeclared (pr_id id ++ str " already exists");
  let impl,opaq,cst = match d with (* Fails if not well-typed *)
    | SectionLocalAssum (ty, impl) ->
        let cst = Global.push_named_assum (id,ty) in
	let impl = if impl then Implicit else Explicit in
	impl, true, cst
    | SectionLocalDef de ->
        let cst = Global.push_named_def (id,de) in
        Explicit, de.const_entry_opaque, cst in
  Nametab.push (Nametab.Until 1) (restrict_path 0 sp) (VarRef id);
  add_section_variable id impl;
  Dischargedhypsmap.set_discharged_hyps sp [];
  add_variable_data id (p,opaq,cst,mk)

let discharge_variable (_,o) = match o with
  | Inr (id,_) -> Some (Inl (variable_constraints id))
  | Inl _ -> Some o

type variable_obj =
    (Univ.constraints, Id.t * variable_declaration) union

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
        match Lazyconstr.get_opaque_future_constraints lc with
        | Some f when Future.is_val f -> Global.add_constraints (Future.force f)
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
  add_section_constant kn' (Global.lookup_constant kn').const_hyps;
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
  let hyps = section_segment_of_constant con in
  let new_hyps = (discharged_hyps kn hyps) @ obj.cst_hyps in
  let abstract = named_of_variable_context hyps in
  let new_decl = GlobalRecipe{ from; info = { Lazyconstr.modlist; abstract }} in
  Some { obj with cst_hyps = new_hyps; cst_decl = new_decl; }

(* Hack to reduce the size of .vo: we keep only what load/open needs *)
let dummy_constant_entry = ConstantEntry (ParameterEntry (None,mkProp,None))

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

let declare_scheme = ref (fun _ _ -> assert false)
let set_declare_scheme f = declare_scheme := f
let declare_sideff se =
  let cbl, scheme = match se with
    | SEsubproof (c, cb) -> [c, cb], None
    | SEscheme (cbl, k) ->
        List.map (fun (_,c,cb) -> c,cb) cbl, Some (List.map pi1 cbl,k) in
  let id_of c = Names.Label.to_id (Names.Constant.label c) in
  let pt_opaque_of cb =
    match cb with
    | { const_body = Def sc } -> Lazyconstr.force sc, false
    | { const_body = OpaqueDef fc } -> Lazyconstr.force_opaque fc, true
    | { const_body = Undef _ } -> anomaly(str"Undefined side effect")
  in
  let ty_of cb =
    match cb.Declarations.const_type with
    | Declarations.NonPolymorphicType t -> Some t
    | _ -> None in
  let cst_of cb =
    let pt, opaque = pt_opaque_of cb in
    let ty = ty_of cb in
    { cst_decl = ConstantEntry (DefinitionEntry {
        const_entry_body = Future.from_here (pt, Declareops.no_seff);
        const_entry_secctx = Some cb.Declarations.const_hyps;
        const_entry_type = ty;
        const_entry_opaque = opaque;
        const_entry_inline_code = false;
        const_entry_feedback = None;
    });
    cst_hyps = [] ;
    cst_kind =  Decl_kinds.IsDefinition Decl_kinds.Definition;
    cst_locl = true;
  } in
  let knl =
    List.map (fun (c,cb) ->
      declare_constant_common (id_of c) (cst_of cb)) cbl in
  match scheme with
  | None -> ()
  | Some (inds,kind) ->
      !declare_scheme kind (Array.of_list (List.combine inds knl))

let declare_constant ?(internal = UserVerbose) ?(local = false) id (cd, kind) =
  let cd = (* We deal with side effects of non-opaque constants *)
    match cd with
    | Entries.DefinitionEntry ({
      const_entry_opaque = false; const_entry_body = bo } as de) ->
        let pt, seff = Future.force bo in
        if Declareops.side_effects_is_empty seff then cd
        else begin
          Declareops.iter_side_effects declare_sideff seff;
          Entries.DefinitionEntry { de with
            const_entry_body = Future.from_val (pt, Declareops.no_seff) }
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
  let () = if_xml (Hook.get f_xml_declare_constant) (internal, kn) in
  kn

let declare_definition ?(internal=UserVerbose)
  ?(opaque=false) ?(kind=Decl_kinds.Definition) ?(local = false)
  id ?types body =
  let cb = 
    { Entries.const_entry_body = body;
      const_entry_type = types;
      const_entry_opaque = opaque;
      const_entry_inline_code = false;
      const_entry_secctx = None;
      const_entry_feedback = None }
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
  add_section_kn kn' (Global.lookup_mind kn').mind_hyps;
  Dischargedhypsmap.set_discharged_hyps sp dhyps;
  List.iter (fun (sp, ref) -> Nametab.push (Nametab.Until 1) sp ref) names

let discharge_inductive ((sp,kn),(dhyps,mie)) =
  let mind = Global.mind_of_delta_kn kn in
  let mie = Global.lookup_mind mind in
  let repl = replacement_context () in
  let sechyps = section_segment_of_mutual_inductive mind in
  Some (discharged_hyps kn sechyps,
        Discharge.process_inductive (named_of_variable_context sechyps) repl mie)

let dummy_one_inductive_entry mie = {
  mind_entry_typename = mie.mind_entry_typename;
  mind_entry_arity = mkProp;
  mind_entry_consnames = mie.mind_entry_consnames;
  mind_entry_lc = []
}

(* Hack to reduce the size of .vo: we keep only what load/open needs *)
let dummy_inductive_entry (_,m) = ([],{
  mind_entry_params = [];
  mind_entry_record = false;
  mind_entry_finite = true;
  mind_entry_inds = List.map dummy_one_inductive_entry m.mind_entry_inds })

type inductive_obj = Dischargedhypsmap.discharged_hyps * mutual_inductive_entry

let inInductive : inductive_obj -> obj =
  declare_object {(default_object "INDUCTIVE") with
    cache_function = cache_inductive;
    load_function = load_inductive;
    open_function = open_inductive;
    classify_function = (fun a -> Substitute (dummy_inductive_entry a));
    subst_function = ident_subst_function;
    discharge_function = discharge_inductive }

(* for initial declaration *)
let declare_mind isrecord mie =
  let id = match mie.mind_entry_inds with
    | ind::_ -> ind.mind_entry_typename
    | [] -> anomaly (Pp.str "cannot declare an empty list of inductives") in
  let (sp,kn as oname) = add_leaf id (inInductive ([],mie)) in
  let mind = Global.mind_of_delta_kn kn in
  declare_mib_implicits mind;
  declare_inductive_argument_scopes mind mie;
  if_xml (Hook.get f_xml_declare_inductive) (isrecord,oname);
  oname

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
