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

(**********************************************)

(* For [DischargeAt (dir,n)], [dir] is the minimum prefix that a
   construction keeps in its name (if persistent), or the section name
   beyond which it is discharged (if volatile); the integer [n]
   (useful only for persistent constructions), is the length of the section
   part in [dir] *)

type strength = 
  | NotDeclare
  | DischargeAt of dir_path * int
  | NeverDischarge

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

let cache_variable (sp,(id,(p,d,str))) =
  (* Constr raisonne sur les noms courts *)
  if Idmap.mem id !vartab then
    errorlabstrm "cache_variable" [< pr_id id; 'sTR " already exists" >];
  let cst = match d with (* Fails if not well-typed *)
    | SectionLocalAssum ty -> Global.push_named_assum (id,ty)
    | SectionLocalDef (c,t) -> Global.push_named_def (id,c,t) in
  let (_,bd,ty) = Global.lookup_named id in
  let vd = (bd,ty,cst) in
  Nametab.push 0 (restrict_path 0 sp) (VarRef id);
  vartab := Idmap.add id (p,vd,str) !vartab

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

type constant_declaration = global_declaration * strength

let csttab = ref (Spmap.empty : strength Spmap.t)

let _ = Summary.declare_summary "CONSTANT"
	  { Summary.freeze_function = (fun () -> !csttab);
	    Summary.unfreeze_function = (fun ft -> csttab := ft);
	    Summary.init_function = (fun () -> csttab := Spmap.empty);
	    Summary.survive_section = false }

let cache_constant (sp,(cdt,stre)) =
  (if Nametab.exists_cci sp then
    let (_,id) = repr_path sp in
    errorlabstrm "cache_constant" [< pr_id id; 'sTR " already exists" >]);
  Global.add_constant sp cdt;
  (match stre with
    | DischargeAt (dp,n) when not (is_dirpath_prefix_of dp (Lib.cwd ())) ->
        (* Only qualifications including the sections segment from the current
           section to the discharge section is available for Remark & Fact *)
        Nametab.push (n-Lib.sections_depth()) sp (ConstRef sp)
    | (NeverDischarge| DischargeAt _) -> 
        (* All qualifications of Theorem, Lemma & Definition are visible *)
        Nametab.push 0 sp (ConstRef sp)
    | NotDeclare -> assert false);
  csttab := Spmap.add sp stre !csttab

(* At load-time, the segment starting from the module name to the discharge *)
(* section (if Remark or Fact) is needed to access a construction *)
let load_constant (sp,(ce,stre)) =
  (if Nametab.exists_cci sp then
    let (_,id) = repr_path sp in
    errorlabstrm "cache_constant" [< pr_id id; 'sTR " already exists" >]);
  csttab := Spmap.add sp stre !csttab;
  Nametab.push (depth_of_strength stre + 1) sp (ConstRef sp)

(* Opening means making the name without its module qualification available *)
let open_constant (sp,(_,stre)) =
  let n = depth_of_strength stre in
  Nametab.push n (restrict_path n sp) (ConstRef sp)

(* Hack to reduce the size of .vo: we keep only what load/open needs *)
let dummy_constant_entry = ParameterEntry mkProp

let export_constant (ce,stre) = Some (dummy_constant_entry,stre)

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

let declare_constant id cd =
  (* let cd = hcons_constant_declaration cd in *)
  let sp = add_leaf id (in_constant cd) in
  if is_implicit_args() then declare_constant_implicits sp;
  sp

let redeclare_constant sp (cd,stre) =
  add_absolutely_named_leaf sp (in_constant (GlobalRecipe cd,stre));
  if is_implicit_args() then declare_constant_implicits sp

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
  if Nametab.exists_cci sp then
    let (_,id) = repr_path sp in
    errorlabstrm "cache_inductive" [< pr_id id; 'sTR " already exists" >]

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
  mind_entry_nparams = 0;
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

let declare_mind mie =
  let id = match mie.mind_entry_inds with
    | ind::_ -> ind.mind_entry_typename
    | [] -> anomaly "cannot declare an empty list of inductives"
  in
  let sp = add_leaf id (in_inductive mie) in
  if is_implicit_args() then declare_mib_implicits sp;
  sp


(*s Test and access functions. *)

let is_constant sp = 
  try let _ = Global.lookup_constant sp in true with Not_found -> false

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
  let (p,_,_) = Idmap.find id !vartab in Names.make_path p id

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
  | ConstRef sp -> constant_strength sp
  | VarRef id -> variable_strength id
  | IndRef _ | ConstructRef _ -> NeverDischarge 
