(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Libnames
open Nameops
open Term
open Sign
open Declarations
open Entries
open Inductive
open Indtypes
open Reduction
open Type_errors
open Typeops
open Libobject
open Lib
open Impargs
open Nametab
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

let if_xml f x = if !Options.xml_export then f x else ()

let set_xml_declare_variable f = xml_declare_variable := if_xml f
let set_xml_declare_constant f = xml_declare_constant := if_xml f
let set_xml_declare_inductive f = xml_declare_inductive := if_xml f

(* Section variables. *)

type section_variable_entry =
  | SectionLocalDef of constr * types option * bool (* opacity *)
  | SectionLocalAssum of types

type variable_declaration = dir_path * section_variable_entry * local_kind

type checked_section_variable =
  | CheckedSectionLocalDef of constr * types * Univ.constraints * bool
  | CheckedSectionLocalAssum of types * Univ.constraints

type checked_variable_declaration = 
    dir_path * checked_section_variable * local_kind

let vartab = ref (Idmap.empty : checked_variable_declaration Idmap.t)

let _ = Summary.declare_summary "VARIABLE"
	  { Summary.freeze_function = (fun () -> !vartab);
	    Summary.unfreeze_function = (fun ft -> vartab := ft);
	    Summary.init_function = (fun () -> vartab := Idmap.empty);
	    Summary.survive_module = false;
	    Summary.survive_section = false }

let cache_variable ((sp,_),(id,(p,d,mk))) =
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
  Nametab.push (Nametab.Until 1) (restrict_path 0 sp) (VarRef id);
  vartab := Idmap.add id (p,vd,mk) !vartab

let (in_variable, out_variable) =
  declare_object { (default_object "VARIABLE") with
    cache_function = cache_variable;
    classify_function = (fun _ -> Dispose) }

let declare_variable_common id obj =
  let oname = add_leaf id (in_variable (id,obj)) in
  declare_var_implicits id;
  Symbols.declare_ref_arguments_scope (VarRef id);
  oname

(* for initial declaration *)
let declare_variable id obj =
  let (sp,kn as oname) = declare_variable_common id obj in
  !xml_declare_variable oname;
  Dischargedhypsmap.set_discharged_hyps sp [];
  oname

(* when coming from discharge: no xml output *)
let redeclare_variable id discharged_hyps obj =
  let oname = declare_variable_common id obj in
  Dischargedhypsmap.set_discharged_hyps (fst oname) discharged_hyps

(* Globals: constants and parameters *)

type constant_declaration = constant_entry * global_kind

let csttab = ref (Spmap.empty : global_kind Spmap.t)

let _ = Summary.declare_summary "CONSTANT"
	  { Summary.freeze_function = (fun () -> !csttab);
	    Summary.unfreeze_function = (fun ft -> csttab := ft);
	    Summary.init_function = (fun () -> csttab := Spmap.empty);
	    Summary.survive_module = false;
	    Summary.survive_section = false }

let cache_constant ((sp,kn),(cdt,kind)) =
  (if Idmap.mem (basename sp) !vartab then
    errorlabstrm "cache_constant" 
      (pr_id (basename sp) ++ str " already exists"));
  (if Nametab.exists_cci sp then
    let (_,id) = repr_path sp in
    errorlabstrm "cache_constant" (pr_id id ++ str " already exists"));
  let _,dir,_ = repr_kn kn in
  let kn' = Global.add_constant dir (basename sp) cdt in
    if kn' <> kn then
      anomaly "Kernel and Library names do not match";
  Nametab.push (Nametab.Until 1) sp (ConstRef kn);
  csttab := Spmap.add sp kind !csttab

(* At load-time, the segment starting from the module name to the discharge *)
(* section (if Remark or Fact) is needed to access a construction *)
let load_constant i ((sp,kn),(_,kind)) =
  (if Nametab.exists_cci sp then
    let (_,id) = repr_path sp in
    errorlabstrm "cache_constant" (pr_id id ++ str " already exists"));
  csttab := Spmap.add sp kind !csttab;
  Nametab.push (Nametab.Until i) sp (ConstRef kn)

(* Opening means making the name without its module qualification available *)
let open_constant i ((sp,kn),_) =
  Nametab.push (Nametab.Exactly i) sp (ConstRef kn)

(* Hack to reduce the size of .vo: we keep only what load/open needs *)
let dummy_constant_entry = ConstantEntry (ParameterEntry mkProp)

let dummy_constant (ce,mk) = dummy_constant_entry,mk

let export_constant cst = Some (dummy_constant cst)

let classify_constant (_,cst) = Substitute (dummy_constant cst)

let (in_constant, out_constant) =
  declare_object { (default_object "CONSTANT") with
    cache_function = cache_constant;
    load_function = load_constant;
    open_function = open_constant;
    classify_function = classify_constant;
    subst_function = ident_subst_function;
    export_function = export_constant } 

let hcons_constant_declaration = function
  | DefinitionEntry ce ->
      let (hcons1_constr,_) = hcons_constr (hcons_names()) in
      DefinitionEntry
       { const_entry_body = hcons1_constr ce.const_entry_body;
	 const_entry_type = option_app hcons1_constr ce.const_entry_type;
         const_entry_opaque = ce.const_entry_opaque }
  | cd -> cd

let declare_constant_common id discharged_hyps (cd,kind) =
  let (sp,kn as oname) = add_leaf id (in_constant (cd,kind)) in
  declare_constant_implicits kn;
  Symbols.declare_ref_arguments_scope (ConstRef kn);
  Dischargedhypsmap.set_discharged_hyps sp discharged_hyps;
  oname

let declare_constant_gen internal id (cd,kind) =
  let cd = hcons_constant_declaration cd in
  let oname = declare_constant_common id [] (ConstantEntry cd,kind) in
  !xml_declare_constant (internal,oname);
  oname

let declare_internal_constant = declare_constant_gen true
let declare_constant = declare_constant_gen false

(* when coming from discharge *)
let redeclare_constant id discharged_hyps (cd,kind) =
  let _ = declare_constant_common id discharged_hyps (GlobalRecipe cd,kind) in
  ()

(* Inductives. *)

let inductive_names sp kn mie =
  let (dp,_) = repr_path sp in
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
  (if Idmap.mem (basename sp) !vartab then
    errorlabstrm "cache_inductive" 
      (pr_id (basename sp) ++ str " already exists"));
  if Nametab.exists_cci sp then
    let (_,id) = repr_path sp in
    errorlabstrm "cache_inductive" (pr_id id ++ str " already exists")

let cache_inductive ((sp,kn),mie) =
  let names = inductive_names sp kn mie in
  List.iter check_exists_inductive names;
  let _,dir,_ = repr_kn kn in
  let kn' = Global.add_mind dir (basename sp) mie in
    if kn' <> kn then
      anomaly "Kernel and Library names do not match";

  List.iter 
    (fun (sp, ref) -> Nametab.push (Nametab.Until 1) sp ref)
    names

let load_inductive i ((sp,kn),mie) =
  let names = inductive_names sp kn mie in
  List.iter check_exists_inductive names;
  List.iter (fun (sp, ref) -> Nametab.push (Nametab.Until i) sp ref) names

let open_inductive i ((sp,kn),mie) =
  let names = inductive_names sp kn mie in
(*  List.iter (fun (sp, ref) -> Nametab.push 0 (restrict_path 0 sp) ref) names*)
  List.iter (fun (sp, ref) -> Nametab.push (Nametab.Exactly i) sp ref) names

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
  declare_object {(default_object "INDUCTIVE") with 
    cache_function = cache_inductive;
    load_function = load_inductive;
    open_function = open_inductive;
    classify_function = (fun (_,a) -> Substitute (dummy_inductive_entry a));
    subst_function = ident_subst_function;
    export_function = export_inductive } 

let declare_inductive_argument_scopes kn mie =
  list_iter_i (fun i {mind_entry_consnames=lc} ->
    Symbols.declare_ref_arguments_scope (IndRef (kn,i));
    for j=1 to List.length lc do
      Symbols.declare_ref_arguments_scope (ConstructRef ((kn,i),j));
    done) mie.mind_entry_inds

let declare_inductive_common mie =
  let id = match mie.mind_entry_inds with
    | ind::_ -> ind.mind_entry_typename
    | [] -> anomaly "cannot declare an empty list of inductives"
  in
  let oname = add_leaf id (in_inductive mie) in
  declare_mib_implicits (snd oname);
  declare_inductive_argument_scopes (snd oname) mie;
  oname

(* for initial declaration *)
let declare_mind isrecord mie =
  let (sp,kn as oname) = declare_inductive_common mie in
  Dischargedhypsmap.set_discharged_hyps sp [] ;
  !xml_declare_inductive (isrecord,oname);
  oname

(* when coming from discharge: no xml output *)
let redeclare_inductive discharged_hyps mie =
 let oname = declare_inductive_common mie in
 Dischargedhypsmap.set_discharged_hyps (fst oname) discharged_hyps ;
 oname

(*s Test and access functions. *)

let is_constant sp = 
  try let _ = Spmap.find sp !csttab in true with Not_found -> false

let constant_strength sp = Global
let constant_kind sp = Spmap.find sp !csttab

let get_variable id = 
  let (p,x,_) = Idmap.find id !vartab in
  match x with
    | CheckedSectionLocalDef (c,ty,cst,opaq) -> (id,Some c,ty)
    | CheckedSectionLocalAssum (ty,cst) -> (id,None,ty)

let get_variable_with_constraints id = 
  let (p,x,_) = Idmap.find id !vartab in
  match x with
    | CheckedSectionLocalDef (c,ty,cst,opaq) -> ((id,Some c,ty),cst)
    | CheckedSectionLocalAssum (ty,cst) -> ((id,None,ty),cst)

let variable_strength _ = Local

let find_section_variable id =
  let (p,_,_) = Idmap.find id !vartab in Libnames.make_path p id

let variable_opacity id =
  let (_,x,_) = Idmap.find id !vartab in
  match x with
    | CheckedSectionLocalDef (c,ty,cst,opaq) -> opaq
    | CheckedSectionLocalAssum (ty,cst) -> false (* any.. *)

let variable_kind id =
  pi3 (Idmap.find id !vartab)

let clear_proofs sign =
  List.map
    (fun (id,c,t as d) -> if variable_opacity id then (id,None,t) else d) sign

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

let last_section_hyps dir =
  fold_named_context
    (fun (id,_,_) sec_ids ->
      try
        let (p,_,_) = Idmap.find id !vartab in
        if dir=p then id::sec_ids else sec_ids
      with Not_found -> sec_ids)
    (Environ.named_context (Global.env()))
    ~init:[]

let is_section_variable = function
  | VarRef _ -> true
  | _ -> false

let strength_of_global = function
  | VarRef _ -> Local
  | IndRef _ | ConstructRef _ | ConstRef _ -> Global
