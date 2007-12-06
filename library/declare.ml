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

(* Strength *)

open Nametab

let strength_min (stre1,stre2) =
  if stre1 = Local or stre2 = Local then Local else Global

let string_of_strength = function
  | Local -> "(local)"
  | Global -> "(global)"

(* XML output hooks *)
let xml_declare_variable = ref (fun (sp:object_name) -> ())
let xml_declare_constant = ref (fun (sp:bool * constant)-> ())
let xml_declare_inductive = ref (fun (sp:bool * object_name) -> ())

let if_xml f x = if !Flags.xml_export then f x else ()

let set_xml_declare_variable f = xml_declare_variable := if_xml f
let set_xml_declare_constant f = xml_declare_constant := if_xml f
let set_xml_declare_inductive f = xml_declare_inductive := if_xml f

(* Section variables. *)

type section_variable_entry =
  | SectionLocalDef of constr * types option * bool (* opacity *)
  | SectionLocalAssum of types

type variable_declaration = dir_path * section_variable_entry * logical_kind

type checked_section_variable =
  | CheckedSectionLocalDef of constr * types * Univ.constraints * bool
  | CheckedSectionLocalAssum of types * Univ.constraints

type checked_variable_declaration = 
    dir_path * checked_section_variable * logical_kind

let vartab = ref (Idmap.empty : checked_variable_declaration Idmap.t)

let _ = Summary.declare_summary "VARIABLE"
  { Summary.freeze_function = (fun () -> !vartab);
    Summary.unfreeze_function = (fun ft -> vartab := ft);
    Summary.init_function = (fun () -> vartab := Idmap.empty);
    Summary.survive_module = false;
    Summary.survive_section = false }

let cache_variable ((sp,_),o) =
  match o with
  | Inl cst -> Global.add_constraints cst
  | Inr (id,(p,d,mk)) ->
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
        CheckedSectionLocalDef (Option.get bd,ty,cst,opaq) in
  Nametab.push (Nametab.Until 1) (restrict_path 0 sp) (VarRef id);
  add_section_variable id;
  Dischargedhypsmap.set_discharged_hyps sp [];
  vartab := Idmap.add id (p,vd,mk) !vartab

let get_variable_constraints id = 
  match pi2 (Idmap.find id !vartab) with
  | CheckedSectionLocalDef (c,ty,cst,opaq) -> cst
  | CheckedSectionLocalAssum (ty,cst) -> cst

let discharge_variable (_,o) = match o with
  | Inr (id,_) -> Some (Inl (get_variable_constraints id))
  | Inl _ -> Some o

let (in_variable, out_variable) =
  declare_object { (default_object "VARIABLE") with
    cache_function = cache_variable;
    discharge_function = discharge_variable;
    classify_function = (fun _ -> Dispose) }

(* for initial declaration *)
let declare_variable id obj =
  let oname = add_leaf id (in_variable (Inr (id,obj))) in
  declare_var_implicits id;
  Notation.declare_ref_arguments_scope (VarRef id);
  !xml_declare_variable oname;
  oname

(* Globals: constants and parameters *)

type constant_declaration = constant_entry * logical_kind

let csttab = ref (Spmap.empty : logical_kind Spmap.t)

let _ = Summary.declare_summary "CONSTANT"
	  { Summary.freeze_function = (fun () -> !csttab);
	    Summary.unfreeze_function = (fun ft -> csttab := ft);
	    Summary.init_function = (fun () -> csttab := Spmap.empty);
	    Summary.survive_module = false;
	    Summary.survive_section = false }

(* At load-time, the segment starting from the module name to the discharge *)
(* section (if Remark or Fact) is needed to access a construction *)
let load_constant i ((sp,kn),(_,_,kind)) =
  if Nametab.exists_cci sp then
    errorlabstrm "cache_constant" 
      (pr_id (basename sp) ++ str " already exists");
  Nametab.push (Nametab.Until i) sp (ConstRef (constant_of_kn kn));
  csttab := Spmap.add sp kind !csttab

(* Opening means making the name without its module qualification available *)
let open_constant i ((sp,kn),_) =
  Nametab.push (Nametab.Exactly i) sp (ConstRef (constant_of_kn kn))

let cache_constant ((sp,kn),(cdt,dhyps,kind)) =
  let id = basename sp in
  let _,dir,_ = repr_kn kn in
  if Idmap.mem id !vartab or Nametab.exists_cci sp then
    errorlabstrm "cache_constant" (pr_id id ++ str " already exists");
  let kn' = Global.add_constant dir id cdt in
  assert (kn' = constant_of_kn kn);
  Nametab.push (Nametab.Until 1) sp (ConstRef (constant_of_kn kn));
  add_section_constant kn' (Global.lookup_constant kn').const_hyps;
  Dischargedhypsmap.set_discharged_hyps sp dhyps;
  csttab := Spmap.add sp kind !csttab

(*s Registration as global tables and rollback. *)

open Cooking

let discharged_hyps kn sechyps =
  let (_,dir,_) = repr_kn kn in
  let args = array_map_to_list destVar (instance_from_named_context sechyps) in
  List.rev (List.map (Libnames.make_path dir) args)

let discharge_constant ((sp,kn),(cdt,dhyps,kind)) =
  let con = constant_of_kn kn in
  let cb = Global.lookup_constant con in
  let repl = replacement_context () in
  let sechyps = section_segment_of_constant con in
  let recipe = { d_from=cb; d_modlist=repl; d_abstract=sechyps } in
  Some (GlobalRecipe recipe,(discharged_hyps kn sechyps)@dhyps,kind)

(* Hack to reduce the size of .vo: we keep only what load/open needs *)
let dummy_constant_entry = ConstantEntry (ParameterEntry (mkProp,false))

let dummy_constant (ce,_,mk) = dummy_constant_entry,[],mk

let export_constant cst = Some (dummy_constant cst)

let classify_constant (_,cst) = Substitute (dummy_constant cst)

let (in_constant, out_constant) =
  declare_object { (default_object "CONSTANT") with
    cache_function = cache_constant;
    load_function = load_constant;
    open_function = open_constant;
    classify_function = classify_constant;
    subst_function = ident_subst_function;
    discharge_function = discharge_constant;
    export_function = export_constant } 

let hcons_constant_declaration = function
  | DefinitionEntry ce when !Flags.hash_cons_proofs ->
      let (hcons1_constr,_) = hcons_constr (hcons_names()) in
      DefinitionEntry
       { const_entry_body = hcons1_constr ce.const_entry_body;
	 const_entry_type = Option.map hcons1_constr ce.const_entry_type;
         const_entry_opaque = ce.const_entry_opaque; 
         const_entry_boxed = ce.const_entry_boxed }
  | cd -> cd

let declare_constant_common id dhyps (cd,kind) =
  let (sp,kn) = add_leaf id (in_constant (cd,dhyps,kind)) in
  let kn = constant_of_kn kn in
  declare_constant_implicits kn;
  Notation.declare_ref_arguments_scope (ConstRef kn);
  kn

let declare_constant_gen internal id (cd,kind) =
  let cd = hcons_constant_declaration cd in
  let kn = declare_constant_common id [] (ConstantEntry cd,kind) in
  !xml_declare_constant (internal,kn);
  kn

let declare_internal_constant = declare_constant_gen true
let declare_constant = declare_constant_gen false

(* Inductives. *)

let declare_inductive_argument_scopes kn mie =
  list_iter_i (fun i {mind_entry_consnames=lc} ->
    Notation.declare_ref_arguments_scope (IndRef (kn,i));
    for j=1 to List.length lc do
      Notation.declare_ref_arguments_scope (ConstructRef ((kn,i),j));
    done) mie.mind_entry_inds

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
    errorlabstrm ""
      (pr_id (basename sp) ++ str " already exists"));
  if Nametab.exists_cci sp then
    let (_,id) = repr_path sp in
    errorlabstrm "" (pr_id id ++ str " already exists")

let load_inductive i ((sp,kn),(_,mie)) =
  let names = inductive_names sp kn mie in
  List.iter check_exists_inductive names;
  List.iter (fun (sp, ref) -> Nametab.push (Nametab.Until i) sp ref) names

let open_inductive i ((sp,kn),(_,mie)) =
  let names = inductive_names sp kn mie in
  List.iter (fun (sp, ref) -> Nametab.push (Nametab.Exactly i) sp ref) names

let cache_inductive ((sp,kn),(dhyps,mie)) =
  let names = inductive_names sp kn mie in
  List.iter check_exists_inductive names;
  let id = basename sp in
  let _,dir,_ = repr_kn kn in
  let kn' = Global.add_mind dir id mie in
  assert (kn'=kn);
  add_section_kn kn (Global.lookup_mind kn').mind_hyps;
  Dischargedhypsmap.set_discharged_hyps sp dhyps;
  List.iter (fun (sp, ref) -> Nametab.push (Nametab.Until 1) sp ref) names

let discharge_inductive ((sp,kn),(dhyps,mie)) =
  let mie = Global.lookup_mind kn in
  let repl = replacement_context () in
  let sechyps = section_segment_of_mutual_inductive kn in
  Some (discharged_hyps kn sechyps,
        Discharge.process_inductive sechyps repl mie)

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

let export_inductive x = Some (dummy_inductive_entry x)

let (in_inductive, out_inductive) =
  declare_object {(default_object "INDUCTIVE") with 
    cache_function = cache_inductive;
    load_function = load_inductive;
    open_function = open_inductive;
    classify_function = (fun (_,a) -> Substitute (dummy_inductive_entry a));
    subst_function = ident_subst_function;
    discharge_function = discharge_inductive;
    export_function = export_inductive } 

(* for initial declaration *)
let declare_mind isrecord mie =
  let id = match mie.mind_entry_inds with
    | ind::_ -> ind.mind_entry_typename
    | [] -> anomaly "cannot declare an empty list of inductives" in
  let (sp,kn as oname) = add_leaf id (in_inductive ([],mie)) in
  declare_mib_implicits kn;
  declare_inductive_argument_scopes kn mie;
  !xml_declare_inductive (isrecord,oname);
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
  List.fold_right
    (fun (id,c,t as d) signv -> 
      let d = if variable_opacity id then (id,None,t) else d in
      Environ.push_named_context_val d signv) sign Environ.empty_named_context_val

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
