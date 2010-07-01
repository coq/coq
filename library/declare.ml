(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module is about the low-level declaration of logical objects *)

open Pp
open Util
open Names
open Libnames
open Nameops
open Term
open Sign
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

let xml_declare_variable = ref (fun (sp:object_name) -> ())
let xml_declare_constant = ref (fun (sp:internal_flag * constant)-> ())
let xml_declare_inductive = ref (fun (sp:internal_flag * object_name) -> ())

let if_xml f x = if !Flags.xml_export then f x else ()

let set_xml_declare_variable f = xml_declare_variable := if_xml f
let set_xml_declare_constant f = xml_declare_constant := if_xml f
let set_xml_declare_inductive f = xml_declare_inductive := if_xml f

let cache_hook = ref ignore
let add_cache_hook f = cache_hook := f

(** Declaration of section variables and local definitions *)

type section_variable_entry =
  | SectionLocalDef of constr * types option * bool (* opacity *)
  | SectionLocalAssum of types * bool (* Implicit status *)

type variable_declaration = dir_path * section_variable_entry * logical_kind

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
	let impl = if impl then Lib.Implicit else Lib.Explicit in
	impl, true, cst
    | SectionLocalDef (c,t,opaq) ->
        let cst = Global.push_named_def (id,c,t) in
        Lib.Explicit, opaq, cst in
  Nametab.push (Nametab.Until 1) (restrict_path 0 sp) (VarRef id);
  add_section_variable id impl;
  Dischargedhypsmap.set_discharged_hyps sp [];
  add_variable_data id (p,opaq,cst,mk)

let discharge_variable (_,o) = match o with
  | Inr (id,_) -> Some (Inl (variable_constraints id))
  | Inl _ -> Some o

let (inVariable,_) =
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
  !xml_declare_variable oname;
  oname


(** Declaration of constants and parameters *)

type constant_declaration = constant_entry * logical_kind

(* At load-time, the segment starting from the module name to the discharge *)
(* section (if Remark or Fact) is needed to access a construction *)
let load_constant i ((sp,kn),(_,_,kind)) =
  if Nametab.exists_cci sp then
    alreadydeclared (pr_id (basename sp) ++ str " already exists");
  let con = Global.constant_of_delta (constant_of_kn kn) in
  Nametab.push (Nametab.Until i) sp (ConstRef con);
  add_constant_kind con kind

(* Opening means making the name without its module qualification available *)
let open_constant i ((sp,kn),_) =
  let con = Global.constant_of_delta (constant_of_kn kn) in
    Nametab.push (Nametab.Exactly i) sp (ConstRef con)

let cache_constant ((sp,kn),(cdt,dhyps,kind)) =
  let id = basename sp in
  let _,dir,_ = repr_kn kn in
  if variable_exists id or Nametab.exists_cci sp then
    alreadydeclared (pr_id id ++ str " already exists");
  let kn' = Global.add_constant dir id cdt in
  assert (kn' = constant_of_kn kn);
  Nametab.push (Nametab.Until 1) sp (ConstRef (constant_of_kn kn));
  add_section_constant kn' (Global.lookup_constant kn').const_hyps;
  Dischargedhypsmap.set_discharged_hyps sp dhyps;
  add_constant_kind (constant_of_kn kn) kind;
  !cache_hook sp

let discharged_hyps kn sechyps =
  let (_,dir,_) = repr_kn kn in
  let args = Array.to_list (instance_from_variable_context sechyps) in
  List.rev (List.map (Libnames.make_path dir) args)

let discharge_constant ((sp,kn),(cdt,dhyps,kind)) =
  let con = constant_of_kn kn in
  let cb = Global.lookup_constant con in
  let repl = replacement_context () in
  let sechyps = section_segment_of_constant con in
  let recipe = { d_from=cb; d_modlist=repl; d_abstract=named_of_variable_context sechyps } in
  Some (GlobalRecipe recipe,(discharged_hyps kn sechyps)@dhyps,kind)

(* Hack to reduce the size of .vo: we keep only what load/open needs *)
let dummy_constant_entry = ConstantEntry (ParameterEntry (mkProp,false))

let dummy_constant (ce,_,mk) = dummy_constant_entry,[],mk

let classify_constant cst = Substitute (dummy_constant cst)

let (inConstant,_) =
  declare_object { (default_object "CONSTANT") with
    cache_function = cache_constant;
    load_function = load_constant;
    open_function = open_constant;
    classify_function = classify_constant;
    subst_function = ident_subst_function;
    discharge_function = discharge_constant }

let hcons_constant_declaration = function
  | DefinitionEntry ce when !Flags.hash_cons_proofs ->
      let (hcons1_constr,_) = hcons_constr (hcons_names()) in
      DefinitionEntry
       { const_entry_body = hcons1_constr ce.const_entry_body;
	 const_entry_type = Option.map hcons1_constr ce.const_entry_type;
         const_entry_opaque = ce.const_entry_opaque;
         const_entry_boxed = ce.const_entry_boxed;
	 const_entry_inline_code = ce.const_entry_inline_code }
  | cd -> cd

let declare_constant_common id dhyps (cd,kind) =
  let (sp,kn) = add_leaf id (inConstant (cd,dhyps,kind)) in
  let c = Global.constant_of_delta (constant_of_kn kn) in
  declare_constant_implicits c;
  Heads.declare_head (EvalConstRef c);
  Notation.declare_ref_arguments_scope (ConstRef c);
  c

let declare_constant_gen internal id (cd,kind) =
  let cd = hcons_constant_declaration cd in
  let kn = declare_constant_common id [] (ConstantEntry cd,kind) in
  !xml_declare_constant (internal,kn);
  kn

(* TODO: add a third function to distinguish between KernelVerbose
 * and user Verbose *)
let declare_internal_constant = declare_constant_gen KernelSilent
let declare_constant = declare_constant_gen UserVerbose

(** Declaration of inductive blocks *)

let declare_inductive_argument_scopes kn mie =
  list_iter_i (fun i {mind_entry_consnames=lc} ->
    Notation.declare_ref_arguments_scope (IndRef (kn,i));
    for j=1 to List.length lc do
      Notation.declare_ref_arguments_scope (ConstructRef ((kn,i),j));
    done) mie.mind_entry_inds

let inductive_names sp kn mie =
  let (dp,_) = repr_path sp in
  let kn = Global.mind_of_delta (mind_of_kn kn) in
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

let check_exists_inductive (sp,_) =
  (if variable_exists (basename sp) then
    alreadydeclared (pr_id (basename sp) ++ str " already exists"));
  if Nametab.exists_cci sp then
    let (_,id) = repr_path sp in
    alreadydeclared (pr_id id ++ str " already exists")

let load_inductive i ((sp,kn),(_,mie)) =
  let names = inductive_names sp kn mie in
  List.iter check_exists_inductive names;
  List.iter (fun (sp, ref) -> Nametab.push (Nametab.Until i) sp ref ) names

let open_inductive i ((sp,kn),(_,mie)) =
  let names = inductive_names sp kn mie in
  List.iter (fun (sp, ref) -> Nametab.push (Nametab.Exactly i) sp ref) names

let cache_inductive ((sp,kn),(dhyps,mie)) =
  let names = inductive_names sp kn mie in
  List.iter check_exists_inductive names;
  let id = basename sp in
  let _,dir,_ = repr_kn kn in
  let kn' = Global.add_mind dir id mie in
  assert (kn'= mind_of_kn kn);
  add_section_kn kn' (Global.lookup_mind kn').mind_hyps;
  Dischargedhypsmap.set_discharged_hyps sp dhyps;
  List.iter (fun (sp, ref) -> Nametab.push (Nametab.Until 1) sp ref) names;
  List.iter (fun (sp,_) -> !cache_hook sp) (inductive_names sp kn mie)


let discharge_inductive ((sp,kn),(dhyps,mie)) =
  let mind = (Global.mind_of_delta (mind_of_kn kn)) in
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

let (inInductive,_) =
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
    | [] -> anomaly "cannot declare an empty list of inductives" in
  let (sp,kn as oname) = add_leaf id (inInductive ([],mie)) in
  let mind = (Global.mind_of_delta (mind_of_kn kn)) in
  declare_mib_implicits mind;
  declare_inductive_argument_scopes mind mie;
  !xml_declare_inductive (isrecord,oname);
  oname

(* Declaration messages *)

let pr_rank i = str (ordinal (i+1))

let fixpoint_message indexes l =
  Flags.if_verbose msgnl (match l with
  | [] -> anomaly "no recursive definition"
  | [id] -> pr_id id ++ str " is recursively defined" ++
      (match indexes with
	 | Some [|i|] -> str " (decreasing on "++pr_rank i++str " argument)"
	 | _ -> mt ())
  | l -> hov 0 (prlist_with_sep pr_comma pr_id l ++
		  spc () ++ str "are recursively defined" ++
		  match indexes with
		    | Some a -> spc () ++ str "(decreasing respectively on " ++
			prlist_with_sep pr_comma pr_rank (Array.to_list a) ++
			str " arguments)"
		    | None -> mt ()))

let cofixpoint_message l =
  Flags.if_verbose msgnl (match l with
  | [] -> anomaly "No corecursive definition."
  | [id] -> pr_id id ++ str " is corecursively defined"
  | l -> hov 0 (prlist_with_sep pr_comma pr_id l ++
                    spc () ++ str "are corecursively defined"))

let recursive_message isfix i l =
  (if isfix then fixpoint_message i else cofixpoint_message) l

let definition_message id =
  Flags.if_verbose msgnl (pr_id id ++ str " is defined")

let assumption_message id =
  Flags.if_verbose msgnl (pr_id id ++ str " is assumed")

let register_message id =
  Flags.if_verbose msgnl (pr_id id ++ str " is registered")
