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
open Library
open Safe_typing

(**********************************************)

(* For [DischargeAt (dir,n)], [dir] is the minimum prefix that a
   construction keeps in its name (if persistent), or the section name
   beyond which it is discharged (if volatile); the integer [n]
   (useful only for persistent constructions), is the length of the section
   part in [dir] *)

open Nametab

let depth_of_strength = function
  | DischargeAt (sp',n) -> n
  | NeverDischarge -> 0
  | NotDeclare -> assert false

let make_strength_0 () = 
  let depth = Lib.sections_depth () in
  let cwd = Lib.cwd() in
  if depth > 0 then DischargeAt (cwd, depth) else NeverDischarge

let make_strength_1 () =
  let depth = Lib.sections_depth () in
  let cwd = Lib.cwd() in
  if depth > 1 then DischargeAt (extract_dirpath_prefix 1 cwd, depth-1)
  else NeverDischarge

let make_strength_2 () =
  let depth = Lib.sections_depth () in
  let cwd = Lib.cwd() in
  if depth > 2 then DischargeAt (extract_dirpath_prefix 2 cwd, depth-2)
  else NeverDischarge

let is_less_persistent_strength = function
  | (NeverDischarge,_) -> false
  | (NotDeclare,_) -> false
  | (_,NeverDischarge) -> true
  | (_,NotDeclare) -> true
  | (DischargeAt (sp1,_),DischargeAt (sp2,_)) ->
      is_dirpath_prefix_of sp1 sp2

let strength_min (stre1,stre2) =
  if is_less_persistent_strength (stre1,stre2) then stre1 else stre2

(* Section variables. *)

type section_variable_entry =
  | SectionLocalDef of constr * types option
  | SectionLocalAssum of types

type variable_declaration = dir_path * section_variable_entry * strength

type checked_section_variable = constr option * types * Univ.constraints

type checked_variable_declaration =
    dir_path * checked_section_variable * strength

let vartab = ref (Idmap.empty : checked_variable_declaration Idmap.t)

let _ = Summary.declare_summary "VARIABLE"
	  { Summary.freeze_function = (fun () -> !vartab);
	    Summary.unfreeze_function = (fun ft -> vartab := ft);
	    Summary.init_function = (fun () -> vartab := Idmap.empty);
	    Summary.survive_section = false }

let cache_variable (sp,(id,(p,d,strength))) =
  (* Constr raisonne sur les noms courts *)
  if Idmap.mem id !vartab then
    errorlabstrm "cache_variable" (pr_id id ++ str " already exists");
  let cst = match d with (* Fails if not well-typed *)
    | SectionLocalAssum ty -> Global.push_named_assum (id,ty)
    | SectionLocalDef (c,t) -> Global.push_named_def (id,c,t) in
  let (_,bd,ty) = Global.lookup_named id in
  let vd = (bd,ty,cst) in
  Nametab.push 0 (restrict_path 0 sp) (VarRef id);
  vartab := Idmap.add id (p,vd,strength) !vartab

let (in_variable, out_variable) =
  let od = {
    cache_function = cache_variable;
    load_function = (fun _ -> ());
    open_function = (fun _ -> ());
    export_function = (fun x -> Some x) }
  in
  declare_object ("VARIABLE", od)

let declare_variable id obj =
  let sp = add_leaf id (in_variable (id,obj)) in
  if is_implicit_args() then declare_var_implicits id;
  sp

(* Globals: constants and parameters *)

type constant_declaration = constant_entry * strength

let csttab = ref (Spmap.empty : strength Spmap.t)

let _ = Summary.declare_summary "CONSTANT"
	  { Summary.freeze_function = (fun () -> !csttab);
	    Summary.unfreeze_function = (fun ft -> csttab := ft);
	    Summary.init_function = (fun () -> csttab := Spmap.empty);
	    Summary.survive_section = false }

let cache_constant (sp,(cdt,stre,kn)) =
  (if Idmap.mem (basename sp) !vartab then
    errorlabstrm "cache_constant" 
      (pr_id (basename sp) ++ str " already exists"));
  (if Nametab.exists_cci sp then
    let (_,id) = repr_path sp in
    errorlabstrm "cache_constant" (pr_id id ++ str " already exists"));
  Global.add_constant kn cdt;
  (match stre with
    | DischargeAt (dp,n) when not (is_dirpath_prefix_of dp (Lib.cwd ())) ->
        (* Only qualifications including the sections segment from the current
           section to the discharge section is available for Remark & Fact *)
        Nametab.push (n-Lib.sections_depth()) sp (ConstRef kn)
    | (NeverDischarge| DischargeAt _) -> 
        (* All qualifications of Theorem, Lemma & Definition are visible *)
        Nametab.push 0 sp (ConstRef kn)
    | NotDeclare -> assert false);
  csttab := Spmap.add sp stre !csttab

(* At load-time, the segment starting from the module name to the discharge *)
(* section (if Remark or Fact) is needed to access a construction *)
let load_constant (sp,(ce,stre,kn)) =
  (if Nametab.exists_cci sp then
    let (_,id) = repr_path sp in
    errorlabstrm "cache_constant" (pr_id id ++ str " already exists"));
  csttab := Spmap.add sp stre !csttab;
  Nametab.push (depth_of_strength stre + 1) sp (ConstRef kn)

(* Opening means making the name without its module qualification available *)
let open_constant (sp,(_,stre,kn)) =
  let n = depth_of_strength stre in
(*  Nametab.push n (restrict_path n sp) (ConstRef kn) *)
  Nametab.push n sp (ConstRef kn)

(* Hack to reduce the size of .vo: we keep only what load/open needs *)
let dummy_constant_entry = ConstantEntry (ParameterEntry mkProp)

let export_constant (ce,stre,kn) = Some (dummy_constant_entry,stre,kn)

let (in_constant, out_constant) =
  let od = {
    cache_function = cache_constant;
    load_function = load_constant;
    open_function = open_constant;
    export_function = export_constant } 
  in
  declare_object ("CONSTANT", od)

let hcons_constant_declaration = function
  | (DefinitionEntry ce, stre) ->
      (DefinitionEntry
       { const_entry_body = hcons1_constr ce.const_entry_body;
	 const_entry_type = option_app hcons1_constr ce.const_entry_type;
         const_entry_opaque = ce.const_entry_opaque }, stre)
  | cd -> cd

let declare_constant id (cd,stre) =
  (* let cd = hcons_constant_declaration cd in *)
  let kn = Lib.make_kn id in
  let sp = add_leaf id (in_constant (ConstantEntry cd,stre,kn)) in
  if is_implicit_args() then declare_constant_implicits kn;
  kn

let redeclare_constant id (cd,stre,kn) =
  let _ = add_leaf id (in_constant (GlobalRecipe cd,stre,kn)) in
  if is_implicit_args() then declare_constant_implicits kn

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

let cache_inductive (sp,(kn,mie)) =
  let names = inductive_names sp kn mie in
  List.iter check_exists_inductive names;
  Global.add_mind kn mie;
  List.iter 
    (fun (sp, ref) -> Nametab.push 0 sp ref)
    names

let load_inductive (sp,(kn,mie)) =
  let names = inductive_names sp kn mie in
  List.iter check_exists_inductive names;
  List.iter (fun (sp, ref) -> Nametab.push 1 sp ref) names

let open_inductive (sp,(kn,mie)) =
  let names = inductive_names sp kn mie in
(*  List.iter (fun (sp, ref) -> Nametab.push 0 (restrict_path 0 sp) ref) names*)
  List.iter (fun (sp, ref) -> Nametab.push 0 sp ref) names

let dummy_one_inductive_entry mie = {
  mind_entry_params = [];
  mind_entry_typename = mie.mind_entry_typename;
  mind_entry_arity = mkProp;
  mind_entry_consnames = mie.mind_entry_consnames;
  mind_entry_lc = []
}

(* Hack to reduce the size of .vo: we keep only what load/open needs *)
let dummy_inductive_entry (kn,m) = kn,{
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

let declare_mind mie =
  let id = match mie.mind_entry_inds with
    | ind::_ -> ind.mind_entry_typename
    | [] -> anomaly "cannot declare an empty list of inductives"
  in
  let kn = Lib.make_kn id in  
  let sp = add_leaf id (in_inductive (kn,mie)) in
  if is_implicit_args() then declare_mib_implicits kn;
  kn


(*s Test and access functions. *)

let is_constant sp = 
  try let _ = Spmap.find sp !csttab in true with Not_found -> false

let constant_strength sp = Spmap.find sp !csttab

let get_variable id = 
  let (p,(c,ty,cst),str) = Idmap.find id !vartab in
  ((id,c,ty),str)

let get_variable_with_constraints id = 
  let (p,(c,ty,cst),str) = Idmap.find id !vartab in
  ((id,c,ty),cst,str)

let variable_strength id =
  let (_,_,str) = Idmap.find id !vartab in str

let find_section_variable id =
  let (p,_,_) = Idmap.find id !vartab in Libnames.make_path p id

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
        let (p,_,_) = Idmap.find id !vartab in
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

let construct_reference ctx_opt id =
  match ctx_opt with
    | None -> construct_qualified_reference (make_short_qualid id)
    | Some ctx -> 
	try
	  mkVar (let _ = Sign.lookup_named id ctx in id)
	with Not_found ->
	  construct_qualified_reference (make_short_qualid id)

let global_qualified_reference qid =
  construct_qualified_reference qid

let global_absolute_reference sp = 
  construct_absolute_reference sp

let global_reference_in_absolute_module dir id = 
  constr_of_reference (Nametab.locate_in_absolute_module dir id)

let global_reference id = 
  construct_qualified_reference (make_short_qualid id)

let is_section_variable = function
  | VarRef _ -> true
  | _ -> false

(* TODO temporary hack!!! *)
let rec is_imported_modpath = function
  | MPfile dp -> dp <> (Lib.module_dp ())
(*  | MPdot (mp,_) -> is_imported_modpath mp *)
  | _ -> false

let is_imported_ref = function
  | VarRef _ -> false
  | ConstRef kn 
  | IndRef (kn,_)
  | ConstructRef ((kn,_),_) 
(*  | ModTypeRef ln  *) -> 
      let (mp,_,_) = repr_kn kn in is_imported_modpath mp
(*  | ModRef mp ->
      is_imported_modpath mp
*)
let is_global id =
  try 
    let ref = Nametab.locate (make_short_qualid id) in
      not (is_imported_ref ref)
  with Not_found -> 
    false

let strength_of_global ref = match ref with 
  | ConstRef kn -> constant_strength (full_name ref)
  | VarRef id -> variable_strength id
  | IndRef _ | ConstructRef _ -> NeverDischarge 

let library_part ref =
  let sp = Nametab.sp_of_global None ref in
  let dir,_ = repr_path sp in
  match strength_of_global ref with
  | DischargeAt (dp,n) -> 
      extract_dirpath_prefix n dp
  | NeverDischarge ->
      if is_dirpath_prefix_of dir (Lib.cwd ()) then
	(* Theorem/Lemma not yet (fully) discharged *)
	extract_dirpath_prefix (Lib.sections_depth ()) (Lib.cwd ())
      else
	(* Theorem/Lemma outside its outer section of definition *)
	dir
  | NotDeclare -> assert false

