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
open Identifier
open Names
open Term
open Sign
open Declarations
open Mod_declarations
open Inductive
open Reduction
open Type_errors
open Typeops
open Libnames
open Libobject
open Lib
open Impargs
open Indrec
open Nametab

type strength = 
  | NotDeclare
  | DischargeAt of dir_path
  | NeverDischarge

let make_strength = function
  | [] -> NeverDischarge
  | l  -> DischargeAt l

let make_strength_0 () = make_strength (Lib.cwd())

let make_strength_1 () =
  let cwd = Lib.cwd() in
  let path = try list_firstn (List.length cwd - 1) cwd with Failure _ -> [] in
  make_strength path

let make_strength_2 () =
  let cwd = Lib.cwd() in
  let path = try list_firstn (List.length cwd - 2) cwd with Failure _ -> [] in
  make_strength path


(* Section variables. *)

type section_variable_entry =
  | SectionLocalDef of constr
  | SectionLocalAssum of constr

type sticky = bool

type variable_declaration = section_variable_entry * strength * sticky

let vartab =
  ref ((Idmap.empty, []) :
       (section_path * variable_declaration) Idmap.t * identifier list)

let current_section_context () = snd !vartab

let _ = Summary.declare_summary "VARIABLE"
	  { Summary.freeze_function = (fun () -> !vartab);
	    Summary.unfreeze_function = (fun ft -> vartab := ft);
	    Summary.init_function = (fun () -> vartab := (Idmap.empty, []));
	    Summary.survive_section = false }

let cache_variable (sp,(d,_,_ as vd)) =
(*
  if Nametab.exists_cci sp then
*)
  (* Constr raisonne sur les noms courts *)
  let id = basename sp in
  if List.mem id (current_section_context ()) then
    errorlabstrm "cache_variable"
      [< pr_id (basename sp); 'sTR " already exists" >];
  begin match d with (* Fails if not well-typed *)
    | SectionLocalAssum ty -> Global.push_named_assum (id,ty)
    | SectionLocalDef c -> Global.push_named_def (id,c)
  end;
  Nametab.push_short_name id (VarRef id);
  vartab := let (m,l) = !vartab in (Idmap.add id (sp,vd) m, id::l)

let (in_variable, out_variable) =
  let od = {
    cache_function = cache_variable;
    load_function = (fun _ -> ());
    open_function = (fun _ -> ());
    export_function = (fun x -> Some x) }
  in
  declare_object ("VARIABLE", od)

let declare_variable id vd =
  let sp = add_leaf id CCI (in_variable vd) in
  if is_implicit_args() then declare_var_implicits id;
  id

(* Parameters. *)
(*
let cache_parameter (sp,c) =
  if Nametab.exists_cci sp then
    errorlabstrm "cache_parameter"
      [< pr_id (basename sp); 'sTR " already exists" >];
  Global.add_parameter sp c (current_section_context ());
  Nametab.push sp (ConstRef sp);
  Nametab.push_short_name (basename sp) (ConstRef sp)

let load_parameter (sp,_) =
  if Nametab.exists_cci sp then
    errorlabstrm "cache_parameter"
      [< pr_id (basename sp); 'sTR " already exists" >];
  Nametab.push sp (ConstRef sp)

let open_parameter (sp,_) =
  Nametab.push_short_name (basename sp) (ConstRef sp)

let export_parameter x = Some x

let (in_parameter, out_parameter) =
  let od = {
    cache_function = cache_parameter;
    load_function = load_parameter;
    open_function = open_parameter;
    export_function = export_parameter } 
  in
  declare_object ("PARAMETER", od)

let declare_parameter id c =
  let sp = add_leaf id CCI (in_parameter c) in 
  if is_implicit_args() then declare_constant_implicits sp;
  sp
*)
(* Constants. *)

type constant_declaration_type =
  | ConstantEntry  of constant_entry
  | ConstantRecipe of unit (* Cooking.recipe *)

type opacity = bool

type constant_declaration = constant_declaration_type * strength * opacity

let csttab = ref (LNmap.empty : strength LNmap.t)

let _ = Summary.declare_summary "CONSTANT"
	  { Summary.freeze_function = (fun () -> !csttab);
	    Summary.unfreeze_function = (fun ft -> csttab := ft);
	    Summary.init_function = (fun () -> csttab := LNmap.empty);
	    Summary.survive_section = false }

let cache_constant (sp,(cdt,stre,op)) =
  if Nametab.exists_cci sp then
    errorlabstrm "cache_constant"
      [< pr_id (basename sp); 'sTR " already exists" >] ;
  let sc = current_section_context() in
  match cdt with 
    | ConstantEntry ce -> 
	let ln = Global.add_constant (label_of_ident (basename sp)) ce in
	  Nametab.push sp (ConstRef ln);
	  Nametab.push_short_name (basename sp) (ConstRef ln);
	  if op then Global.set_opaque ln;
	  csttab := LNmap.add ln stre !csttab
    | ConstantRecipe r -> 
	errorlabstrm "cache_constant"
	  [< 'sTR "I forgot sections... " >]
	(* Global.add_discharged_constant sp r sc*)

let load_constant (sp,(ce,stre,op)) = ()
(*  if Nametab.exists_cci sp then
    errorlabstrm "cache_constant"
      [< pr_id (basename sp); 'sTR " already exists" >] ;
  csttab := Spmap.add sp stre !csttab;
  Nametab.push sp (ConstRef sp)
*)

let open_constant (sp,_) = ()
(*  Nametab.push_short_name (basename sp) (ConstRef sp) *)

(* Hack to reduce the size of .vo: we keep only what load/open needs *)
let dummy_constant_entry = ConstantEntry { 
  const_entry_body = None;
  const_entry_type = None }

let export_constant (ce,stre,op) = Some (dummy_constant_entry,stre,op)

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
	 { const_entry_body = option_app hcons1_constr ce.const_entry_body;
	   const_entry_type = option_app hcons1_constr ce.const_entry_type },
	 stre)
  | cd -> cd

let declare_constant id cd =
  (* let cd = hcons_constant_declaration cd in *)
  let sp = add_leaf id CCI (in_constant cd) in
  let cp = Nametab.locate_constant (Libnames.qualid_of_sp sp) in
    if is_implicit_args() then declare_constant_implicits cp;
    cp

(* Inductives. *)


let inductive_names_from_entry sp ln mie =
  let names, _ = 
    List.fold_left
      (fun (names, n) ind ->
	 let ind_p = (ln,n) in
	 let names, _ =
	   List.fold_left
	     (fun (names, p) l ->
		let sp = 
		  Libnames.make_path (dirpath sp) (ident_of_label l) CCI 
		in
		  ((sp, ConstructRef (ind_p,p)) :: names, p+1))
	     (names, 1) ind.mind_entry_consnames in
	 let sp = 
	   Libnames.make_path 
	     (dirpath sp) 
	     (ident_of_label ind.mind_entry_typename) 
	     CCI 
	 in
	   ((sp, IndRef ind_p) :: names, n+1))
      ([], 0) mie.mind_entry_inds
  in names

let check_exists_inductive (sp,_) =
  if Nametab.exists_cci sp then
    errorlabstrm "cache_inductive"
      [< pr_id (basename sp); 'sTR " already exists" >]

let cache_inductive (sp,mie) =
  let ln = Global.add_mind mie in
  let names = inductive_names_from_entry sp ln mie in
  List.iter check_exists_inductive names;
  List.iter (fun (sp, ref) -> Nametab.push sp ref; Nametab.push_short_name
  (basename sp) ref) names

(*let load_inductive (sp,mie) = 
  let names = inductive_names_from_entry sp mie in
  List.iter check_exists_inductive names;
  List.iter (fun (sp, ref) -> Nametab.push sp ref) names

let open_inductive (sp,mie) =
  let names = inductive_names_from_entry sp mie in
  List.iter (fun (sp, ref) -> Nametab.push_short_name (basename sp) ref) names
*)
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
    load_function = (fun _ -> ());  (* *_module will do that *)
    open_function = (fun _ -> ());
    export_function = export_inductive } 
  in
  declare_object ("INDUCTIVE", od)

let declare_mind mie =
  let id = match mie.mind_entry_inds with
    | ind::_ -> ident_of_label ind.mind_entry_typename
    | [] -> anomaly "cannot declare an empty list of inductives"
  in
  let sp = add_leaf id CCI (in_inductive mie) in
  let ln = Nametab.locate_mind (Libnames.qualid_of_sp sp) in
    if is_implicit_args() then declare_mib_implicits ln;
    ln


(* modules and components *)

let inductive_names_from_body sp ln mie =
  let names, _ = 
    Array.fold_left
      (fun (names, n) ind ->
	 let ind_p = (ln,n) in
	 let names, _ =
	   Array.fold_left
	     (fun (names, p) l ->
		let sp = 
		  Libnames.make_path (dirpath sp) (ident_of_label l) CCI 
		in
		  ((sp, ConstructRef (ind_p,p)) :: names, p+1))
	     (names, 1) ind.mind_consnames in
	 let sp = 
	   Libnames.make_path 
	     (dirpath sp) 
	     (ident_of_label ind.mind_typename) 
	     CCI 
	 in
	   ((sp, IndRef ind_p) :: names, n+1))
      ([], 0) mie.mind_packets
  in names

let rec add_signature dir mp signature =
  let add_item (l,item) = 
    let ln = make_ln mp l in
    let id = (ident_of_label l) in
    let sp = Libnames.make_path dir id CCI in
      match item with
	| SPBconst _ -> 
	    if Nametab.exists_cci sp then
	      errorlabstrm "cache_constant"
		[< pr_id (basename sp); 'sTR " already exists" >] ;
	    let ref = ConstRef ln in
	    Nametab.push sp ref;
	    Nametab.push_short_name id ref
	| SPBmind mib -> 
	    let names = inductive_names_from_body sp ln mib in
	    List.iter check_exists_inductive names;
	    List.iter 
	      (fun (sp, ref) -> 
		 Nametab.push sp ref; 
		 Nametab.push_short_name (basename sp) ref) 
	      names
	| SPBmodule _ ->
	    anomaly "No modules today... Too hot."
	| SPBmodtype _ -> 
	    anomaly "No modtypes today... Too hot."
  in
    List.iter add_item signature

let declare_module_components dir mp = 
  let modtype = Modops.scrape_modtype 
		  (Global.env ())
		  (Global.lookup_module mp).mod_type 
  in
    match modtype with
      | MTBident _ -> assert false
      | MTBfunsig _ -> ()
      | MTBsig(_,signature) -> add_signature dir mp signature

(*s Test and access functions. *)

let is_constant sp = 
  try 
    match Nametab.absolute_reference sp with
      | ConstRef _ -> true
      | _ -> false
  with Not_found -> false

let constant_strength sp = LNmap.find sp !csttab

let constant_or_parameter_strength sp =
  try constant_strength sp with Not_found -> NeverDischarge

let get_variable id = 
  let (_,(_,str,sticky)) = Idmap.find id (fst !vartab) in
  let (c,ty) = Global.lookup_named id in
  ((id,c,ty),str,sticky)

let variable_strength id =
  let _,(_,str,_) = Idmap.find id (fst !vartab) in str

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
  | VarRef sp -> []
  | ConstRef sp -> (Global.lookup_constant sp).const_hyps
  | IndRef (sp,_) -> (Global.lookup_mind sp).mind_hyps
  | ConstructRef ((sp,_),_) -> (Global.lookup_mind sp).mind_hyps

(*
let global_sp_operator env sp id =
  try

  with Not_found -> 
    let mib = 
    mind_oper_of_id sp id mib, mib.mind_hyps
*)

(*let rec occur_section_variable id = function
  | id'::_ when id = id' -> true
  | _::l -> occur_section_variable id l
  | [] -> false
*)

let rec quantify_extra_hyps c = function
  | (id,None,t)::hyps ->
      mkNamedLambda id t (quantify_extra_hyps c hyps)
  (* Bugg� car id n'appara�t pas dans les instances des constantes dans c *)
  (* et id n'est donc pas substitu� dans ces constantes *)
  | (id,Some b,t)::hyps ->
      mkNamedLetIn id b t (quantify_extra_hyps c hyps)
  | [] -> c

let find_common_hyps_then_abstract c hyps' hyps =
  let rec find = function
    | (id,_,_) :: hyps when List.mem id hyps' -> find hyps
    | hyps -> quantify_extra_hyps c hyps in
  find (List.rev hyps)

let section_variable_paths () = snd !vartab

let find_section_variable id = 
  let _ = Idmap.find id (fst !vartab) in id

let last_section_hyps dir =
  Idmap.fold
    (fun id (sp,_) hyps -> if dirpath sp = dir then id :: hyps else hyps)
    (fst !vartab) []

let rec find_var id = function
  | [] -> raise Not_found
  | sp::l -> if basename sp = id then sp else find_var id l

let implicit_section_args ref =
  if Options.immediate_discharge then
    let hyps = context_of_global_reference ref in
    let hyps0 = section_variable_paths () in
    let rec keep acc = function
      | (sp,None,_)::hyps ->
	  let acc = if List.mem sp hyps0 then sp::acc else acc in
	  keep acc hyps
      | (_,Some _,_)::hyps -> keep acc hyps
      | [] -> acc
    in keep [] hyps
  else []

let section_hyps ref =
  let hyps = context_of_global_reference ref in
  let hyps0 = section_variable_paths () in
  let rec keep acc = function
    | (sp,b,_ as d)::hyps ->
	let acc = if List.mem sp hyps0 then (sp,b=None)::acc else acc in
	keep acc hyps
    | [] -> acc
  in keep [] hyps

let extract_instance ref args =
  if Options.immediate_discharge then args
  else
  let hyps = context_of_global_reference ref in
  let hyps0 = current_section_context () in
  let na = Array.length args in
  let rec peel n acc = function
    | (id,None,_ as d)::hyps ->
	if List.mem id hyps0 then peel (n-1) acc hyps
	else peel (n-1) (args.(n)::acc) hyps
    | (_,Some _,_)::hyps -> peel n acc hyps
    | [] -> Array.of_list acc
  in peel (na-1) [] hyps

let constr_of_reference _ _ ref =
if Options.immediate_discharge then
  match ref with
    | VarRef id -> mkVar id
    | ConstRef ln -> mkConst (ln,[||])
    | ConstructRef cons_p -> mkMutConstruct (cons_p,[||])
    | IndRef ind_p -> mkMutInd (ind_p,[||])
else
  let hyps = context_of_global_reference ref in
  let hyps0 = current_section_context () in
  let args = instance_from_section_context hyps in
  let body = match ref with
    | VarRef id -> mkVar id
    | ConstRef ln -> mkConst (ln,Array.of_list args)
    | ConstructRef cons_p -> mkMutConstruct (cons_p,Array.of_list args)
    | IndRef ind_p -> mkMutInd (ind_p,Array.of_list args)
  in
  find_common_hyps_then_abstract body hyps0 hyps

let construct_absolute_reference env sp =
  constr_of_reference Evd.empty env (Nametab.absolute_reference sp)

let construct_qualified_reference env qid =
  let ref = Nametab.locate qid in
  constr_of_reference Evd.empty env ref

let construct_reference env id =
  construct_qualified_reference env (make_qualid [] id)

let global_qualified_reference qid =
  construct_qualified_reference (Global.env()) qid

let global_absolute_reference ref = 
  constr_of_reference Evd.empty (Global.env()) ref

let global_reference_in_absolute_module dir id = 
  constr_of_reference Evd.empty (Global.env())
    (Nametab.locate_in_absolute_module dir id)

let global_reference id = 
  construct_reference (Global.env()) id

let is_section_variable = function
  | VarRef _ -> true
  | _ -> false

let rec is_imported_modpath = function
  | MPcomp _ -> true
  | MPdot (mp,_) -> is_imported_modpath mp
  | _ -> false

let is_imported_ref = function
  | VarRef _ -> false
  | ConstRef ln 
  | IndRef (ln,_)
  | ConstructRef ((ln,_),_) -> 
      is_imported_modpath (modname ln)


let is_global id =
  try 
    let ref = Nametab.locate (make_qualid [] id) in
      not (is_imported_ref ref)
  with Not_found -> 
    false

(*let path_of_constructor_path ((ln,tyi),ind) =
  ln
   let mib = Global.lookup_mind sp in
   let mip = mind_nth_type_packet mib tyi in 
   let (pa,_,k) = repr_path sp in 
   Names.make_path pa (mip.mind_consnames.(ind-1)) k 


let path_of_inductive_path (sp,tyi) =
  if tyi = 0 then sp
  else
    let mib = Global.lookup_mind sp in
    let mip = mind_nth_type_packet mib tyi in 
    let (pa,_,k) = repr_path sp in 
    Names.make_path pa (mip.mind_typename) k 
*)
(* Util *)
let instantiate_inductive_section_params t ind =
  if Options.immediate_discharge then 
  let sign = section_hyps (IndRef ind) in
  let rec inst s ctxt t =
    let k = kind_of_term t in
    match (ctxt,k) with
    | (id,true)::ctxt, IsLambda(_,_,t) ->
	inst ((mkVar id)::s) ctxt t
    | (id,false)::ctxt, IsLetIn(_,_,_,t) -> 
	inst ((mkVar id)::s) ctxt t
    | [], _ -> substl s t
    | _ -> anomaly"instantiate_params: term and ctxt mismatch"
  in inst [] sign t
  else t
(* Eliminations. *)

let eliminations = [ (prop,"_ind") ; (spec,"_rec") ; (types,"_rect") ]

let elimination_suffix = function
  | Type _    -> "_rect"
  | Prop Null -> "_ind"
  | Prop Pos  -> "_rec"

let make_elimination_ident id s = add_suffix id (elimination_suffix s)
  
let declare_one_elimination mispec =
  let mindstr = string_of_id (mis_typename mispec) in
  let declare na c =
    (* Hack to get const_hyps right in the declaration *)
    let c = instantiate_inductive_section_params c (fst (mis_inductive mispec))
    in
    let _ = declare_constant (id_of_string na)
      (ConstantEntry { const_entry_body = Some c; const_entry_type = None }, 
       NeverDischarge,false) in
    Options.if_verbose pPNL [< 'sTR na; 'sTR " is defined" >]
  in
  let env = Global.env () in
  let sigma = Evd.empty in
  let elim_scheme = build_indrec env sigma mispec in
  let npars = mis_nparams mispec in
  let make_elim s = instanciate_indrec_scheme s npars elim_scheme in
  let kelim = mis_kelim mispec in
  List.iter
    (fun (sort,suff) -> 
       if List.mem sort kelim then declare (mindstr^suff) (make_elim sort))
    eliminations

let declare_eliminations sp =
  let mib = Global.lookup_mind sp in
(*
  let ids = ids_of_named_context mib.mind_hyps in
  if not (list_subset ids (ids_of_named_context (Global.named_context ()))) then    error ("Declarations of elimination scheme outside the section "^
    "of the inductive definition is not implemented");
*)
  let ctxt = instance_from_section_context mib.mind_hyps in
  for i = 0 to Array.length mib.mind_packets - 1 do
    if mind_type_finite mib i then
      let mispec = Global.lookup_mind_specif ((sp,i), Array.of_list ctxt) in 
      declare_one_elimination mispec
  done

(* Look up function for the default elimination constant *)

let lookup_eliminator env ind_p s =
  let dir, base = repr_qualid (Nametab.get_full_qualid (IndRef ind_p)) in
  let id = add_suffix base (elimination_suffix s) in
  (* Try first to get an eliminator defined in the same section as the *)
  (* inductive type *)
  try construct_absolute_reference env (Libnames.make_path dir id CCI)
  with Not_found ->
  (* Then try to get a user-defined eliminator in some other places *)
  (* using short name (e.g. for "eq_rec") *)
  construct_reference env id
  
