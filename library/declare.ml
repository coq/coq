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
open Names
open Nameops
open Term
open Sign
open Declarations
open Inductive
open Indtypes
open Reduction
open Type_errors
open Typeops
open Libobject
open Lib
open Impargs
open Nametab
open Library
open Safe_typing
open Decl_kinds

(**********************************************)

(* For [DischargeAt (dir,n)], [dir] is the minimum prefix that a
   construction keeps in its name (if persistent), or the section name
   beyond which it is discharged (if volatile); the integer [n]
   (useful only for persistent constructions), is the length of the section
   part in [dir] *)

open Nametab

let strength_min (stre1,stre2) =
  if stre1 = Local or stre2 = Local then Local else Global

let string_of_strength = function
  | Local -> "(local)"
  | Global -> "(global)"

(* XML output hooks *)
let xml_declare_variable = ref (fun sp -> ())
let xml_declare_constant = ref (fun sp -> ())
let xml_declare_inductive = ref (fun sp -> ())

let set_xml_declare_variable f = xml_declare_variable := f
let set_xml_declare_constant f = xml_declare_constant := f
let set_xml_declare_inductive f = xml_declare_inductive := f

(* Section variables. *)

type section_variable_entry =
  | SectionLocalDef of constr * types option * bool (* opacity *)
  | SectionLocalAssum of types

type variable_declaration = dir_path * section_variable_entry * local_kind

type checked_section_variable =
  | CheckedSectionLocalDef of constr * types * Univ.constraints * bool
  | CheckedSectionLocalAssum of types * Univ.constraints

type checked_variable_declaration = dir_path * checked_section_variable

let vartab = ref (Idmap.empty : checked_variable_declaration Idmap.t)

let _ = Summary.declare_summary "VARIABLE"
	  { Summary.freeze_function = (fun () -> !vartab);
	    Summary.unfreeze_function = (fun ft -> vartab := ft);
	    Summary.init_function = (fun () -> vartab := Idmap.empty);
	    Summary.survive_section = false }

let cache_variable (sp,(id,(p,d,mk))) =
  (* Constr raisonne sur les noms courts *)
  if Idmap.mem id !vartab then
    errorlabstrm "cache_variable" (pr_id id ++ str " already exists");
  let vd = match d with (* Fails if not well-typed *)
    | SectionLocalAssum ty ->
        let cst = Global.push_named_assum (id,ty) in
        let (_,bd,ty) = Global.lookup_named id in
        CheckedSectionLocalAssum (ty,cst)
    | SectionLocalDef (c,t,opaq) -> 
        let cst = Global.push_named_def (id,c,t) in
        let (_,bd,ty) = Global.lookup_named id in
        CheckedSectionLocalDef (out_some bd,ty,cst,opaq) in
  Nametab.push 0 (restrict_path 0 sp) (VarRef id);
  vartab := Idmap.add id (p,vd) !vartab

let (in_variable, out_variable) =
  let od = {
    cache_function = cache_variable;
    load_function = (fun _ -> ());
    open_function = (fun _ -> ());
    export_function = (fun x -> Some x) }
  in
  declare_object ("VARIABLE", od)

let declare_variable_common id obj =
  let sp = add_leaf id (in_variable (id,obj)) in
  if is_implicit_args() then declare_var_implicits id;
  sp

(* for initial declaration *)
let declare_variable id obj =
  let sp = declare_variable_common id obj in
  !xml_declare_variable sp;
  Dischargedhypsmap.set_discharged_hyps sp [] ;
  sp

(* when coming from discharge: no xml output *)
let redeclare_variable id discharged_hyps obj =
  let sp = declare_variable_common id obj in
  Dischargedhypsmap.set_discharged_hyps sp discharged_hyps ;
   sp

(* Globals: constants and parameters *)

type constant_declaration = global_declaration * global_kind

let csttab = ref (Spmap.empty : global_kind Spmap.t)

let _ = Summary.declare_summary "CONSTANT"
	  { Summary.freeze_function = (fun () -> !csttab);
	    Summary.unfreeze_function = (fun ft -> csttab := ft);
	    Summary.init_function = (fun () -> csttab := Spmap.empty);
	    Summary.survive_section = false }

let cache_constant (sp,(cdt,kind)) =
  (if Idmap.mem (basename sp) !vartab then
    errorlabstrm "cache_constant" 
      (pr_id (basename sp) ++ str " already exists"));
  (if Nametab.exists_cci sp then
    let (_,id) = repr_path sp in
    errorlabstrm "cache_constant" (pr_id id ++ str " already exists"));
  Global.add_constant sp cdt;
  Nametab.push 0 sp (ConstRef sp);
  csttab := Spmap.add sp kind !csttab

(* At load-time, the segment starting from the module name to the discharge *)
(* section (if Remark or Fact) is needed to access a construction *)
let load_constant (sp,(_,kind)) =
  (if Nametab.exists_cci sp then
    let (_,id) = repr_path sp in
    errorlabstrm "cache_constant" (pr_id id ++ str " already exists"));
  csttab := Spmap.add sp kind !csttab;
  Nametab.push 1 sp (ConstRef sp)

(* Opening means making the name without its module qualification available *)
let open_constant (sp,_) =
  Nametab.push 0 (restrict_path 0 sp) (ConstRef sp)

(* Hack to reduce the size of .vo: we keep only what load/open needs *)
let dummy_constant_entry = ParameterEntry mkProp

let export_constant (ce,mk) = Some (dummy_constant_entry,mk)

let (in_constant, out_constant) =
  let od = {
    cache_function = cache_constant;
    load_function = load_constant;
    open_function = open_constant;
    export_function = export_constant } 
  in
  declare_object ("CONSTANT", od)

let hcons_constant_declaration = function
  | (ConstantEntry ce, stre) ->
      (ConstantEntry
       { const_entry_body = hcons1_constr ce.const_entry_body;
	 const_entry_type = option_app hcons1_constr ce.const_entry_type;
         const_entry_opaque = ce.const_entry_opaque }, stre)
  | cd -> cd

let declare_constant id (cd,kind) =
  (* let cd = hcons_constant_declaration cd in *)
  let sp = add_leaf id (in_constant (cd,kind)) in
  if is_implicit_args() then declare_constant_implicits sp;
  Dischargedhypsmap.set_discharged_hyps sp [] ;
  !xml_declare_constant sp;
  sp

(* when coming from discharge *)

let redeclare_constant sp discharged_hyps (cd,kind) =
  add_absolutely_named_leaf sp (in_constant (GlobalRecipe cd,kind));
  if is_implicit_args() then declare_constant_implicits sp ;
  Dischargedhypsmap.set_discharged_hyps sp discharged_hyps

(* Inductives. *)

let inductive_names sp mie =
  let (dp,_) = repr_path sp in
  let names, _ = 
    List.fold_left
      (fun (names, n) ind ->
	 let indsp = (sp,n) in
	 let names, _ =
	   List.fold_left
	     (fun (names, p) id ->
		let sp = Names.make_path dp id in
		((sp, ConstructRef (indsp,p)) :: names, p+1))
	     (names, 1) ind.mind_entry_consnames in
	 let sp = Names.make_path dp ind.mind_entry_typename in
	 ((sp, IndRef indsp) :: names, n+1))
      ([], 0) mie.mind_entry_inds
  in names

let check_exists_inductive (sp,_) =
  (if Idmap.mem (basename sp) !vartab then
    errorlabstrm "cache_inductive" 
      (pr_id (basename sp) ++ str " already exists"));
  if Nametab.exists_cci sp then
    let (_,id) = repr_path sp in
    errorlabstrm "cache_inductive" (pr_id id ++ str " already exists")

let cache_inductive (sp,mie) =
  let names = inductive_names sp mie in
  List.iter check_exists_inductive names;
  Global.add_mind sp mie;
  List.iter 
    (fun (sp, ref) -> Nametab.push 0 sp ref)
    names

let load_inductive (sp,mie) =
  let names = inductive_names sp mie in
  List.iter check_exists_inductive names;
  List.iter (fun (sp, ref) -> Nametab.push 1 sp ref) names

let open_inductive (sp,mie) =
  let names = inductive_names sp mie in
  List.iter (fun (sp, ref) -> Nametab.push 0 (restrict_path 0 sp) ref) names

let dummy_one_inductive_entry mie = {
  mind_entry_params = [];
  mind_entry_typename = mie.mind_entry_typename;
  mind_entry_arity = mkProp;
  mind_entry_consnames = mie.mind_entry_consnames;
  mind_entry_lc = []
}

(* Hack to reduce the size of .vo: we keep only what load/open needs *)
let dummy_inductive_entry m = {
  mind_entry_finite = true;
  mind_entry_inds = List.map dummy_one_inductive_entry m.mind_entry_inds }

let export_inductive x = Some (dummy_inductive_entry x)

let (in_inductive, out_inductive) =
  let od = {
    cache_function = cache_inductive;
    load_function = load_inductive;
    open_function = open_inductive;
    export_function = export_inductive } 
  in
  declare_object ("INDUCTIVE", od)

let declare_inductive_common mie =
  let id = match mie.mind_entry_inds with
    | ind::_ -> ind.mind_entry_typename
    | [] -> anomaly "cannot declare an empty list of inductives"
  in
  let sp = add_leaf id (in_inductive mie) in
  if is_implicit_args() then declare_mib_implicits sp;
  sp

(* for initial declaration *)
let declare_mind mie =
  let sp = declare_inductive_common mie in
  Dischargedhypsmap.set_discharged_hyps sp [] ;
  !xml_declare_inductive sp;
  sp

(* when coming from discharge: no xml output *)
let redeclare_inductive discharged_hyps mie =
 let sp = declare_inductive_common mie in
 Dischargedhypsmap.set_discharged_hyps sp discharged_hyps ;
 sp

(*s Test and access functions. *)

let is_constant sp = 
  try let _ = Global.lookup_constant sp in true with Not_found -> false

let constant_strength sp = Global
let constant_kind sp = Spmap.find sp !csttab

let get_variable id = 
  let (p,x) = Idmap.find id !vartab in
  match x with
    | CheckedSectionLocalDef (c,ty,cst,opaq) -> (id,Some c,ty)
    | CheckedSectionLocalAssum (ty,cst) -> (id,None,ty)

let get_variable_with_constraints id = 
  let (p,x) = Idmap.find id !vartab in
  match x with
    | CheckedSectionLocalDef (c,ty,cst,opaq) -> ((id,Some c,ty),cst)
    | CheckedSectionLocalAssum (ty,cst) -> ((id,None,ty),cst)

let variable_strength _ = Local

let find_section_variable id =
  let (p,_) = Idmap.find id !vartab in Names.make_path p id

let variable_opacity id =
  let (_,x) = Idmap.find id !vartab in
  match x with
    | CheckedSectionLocalDef (c,ty,cst,opaq) -> opaq
    | CheckedSectionLocalAssum (ty,cst) -> false (* any.. *)

(* Global references. *)

let first f v =
  let n = Array.length v in
  let rec look_for i =
    if i = n then raise Not_found;
    try f i v.(i) with Not_found -> look_for (succ i)
  in
  look_for 0

let mind_oper_of_id sp id mib =
  first
    (fun tyi mip ->
       if id = mip.mind_typename then 
	 IndRef (sp,tyi)
       else
	 first 
	   (fun cj cid -> 
	      if id = cid then 
		ConstructRef ((sp,tyi),succ cj) 
	      else raise Not_found) 
	   mip.mind_consnames)
    mib.mind_packets

let context_of_global_reference = function
  | VarRef id -> []
  | ConstRef sp -> (Global.lookup_constant sp).const_hyps
  | IndRef (sp,_) -> (Global.lookup_mind sp).mind_hyps
  | ConstructRef ((sp,_),_) -> (Global.lookup_mind sp).mind_hyps

let reference_of_constr c = match kind_of_term c with
  | Const sp -> ConstRef sp
  | Ind ind_sp -> IndRef ind_sp
  | Construct cstr_cp -> ConstructRef cstr_cp
  | Var id -> VarRef id
  |  _ -> raise Not_found

let last_section_hyps dir =
  fold_named_context
    (fun (id,_,_) sec_ids ->
      try
        let (p,_) = Idmap.find id !vartab in
        if dir=p then id::sec_ids else sec_ids
      with Not_found -> sec_ids)
    (Environ.named_context (Global.env()))
    ~init:[]

let constr_of_reference = function
  | VarRef id -> mkVar id
  | ConstRef sp -> mkConst sp
  | ConstructRef sp -> mkConstruct sp
  | IndRef sp -> mkInd sp

let construct_absolute_reference sp =
  constr_of_reference (Nametab.absolute_reference sp)

let construct_qualified_reference qid =
  let ref = Nametab.locate qid in
  constr_of_reference ref

let construct_reference env id =
  try
    mkVar (let _ = Environ.lookup_named id env in id)
  with Not_found ->
    let ref = Nametab.sp_of_id id in
    constr_of_reference ref

let global_qualified_reference qid =
  construct_qualified_reference qid

let global_absolute_reference sp = 
  construct_absolute_reference sp

let global_reference_in_absolute_module dir id = 
  constr_of_reference (Nametab.locate_in_absolute_module dir id)

let global_reference id = 
  construct_reference (Global.env()) id

let dirpath sp = let (p,_) = repr_path sp in p

let dirpath_of_global = function
  | VarRef id -> empty_dirpath
  | ConstRef sp -> dirpath sp
  | IndRef (sp,_) -> dirpath sp
  | ConstructRef ((sp,_),_) -> dirpath sp

let is_section_variable = function
  | VarRef _ -> true
  | _ -> false

let is_global id =
  try 
    let osp = Nametab.locate (make_short_qualid id) in
    (* Compatibilité V6.3: Les variables de section ne sont pas globales
    not (is_section_variable osp) && *)
    is_dirpath_prefix_of (dirpath_of_global osp) (Lib.cwd())
  with Not_found -> 
    false

let strength_of_global = function
  | VarRef _ -> Local
  | IndRef _ | ConstructRef _ | ConstRef _ -> Global

let library_part ref =
  let sp = Nametab.sp_of_global (Global.env ()) ref in
  let dir,_ = repr_path sp in
  match strength_of_global ref with
  | Local -> 
      anomaly "TODO";
      extract_dirpath_prefix (Lib.sections_depth ()) (Lib.cwd ())
  | Global ->
      if is_dirpath_prefix_of dir (Lib.cwd ()) then
        (* Not yet (fully) discharged *)
        extract_dirpath_prefix (Lib.sections_depth ()) (Lib.cwd ())
      else
	(* Theorem/Lemma outside its outer section of definition *)
	dir
