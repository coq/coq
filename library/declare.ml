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
open Term
open Sign
open Declarations
open Inductive
open Reduction
open Type_errors
open Typeops
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
  ref ((Spmap.empty, []) :
       (identifier * variable_declaration) Spmap.t * section_path list)

let current_section_context () =
  List.map (fun sp -> (basename sp, sp)) (snd !vartab)

let _ = Summary.declare_summary "VARIABLE"
	  { Summary.freeze_function = (fun () -> !vartab);
	    Summary.unfreeze_function = (fun ft -> vartab := ft);
	    Summary.init_function = (fun () -> vartab := (Spmap.empty, []));
	    Summary.survive_section = false }

let cache_variable (sp,(id,(d,_,_) as vd)) =
  if Nametab.exists_cci sp then
    errorlabstrm "cache_variable"
      [< pr_id (basename sp); 'sTR " already exists" >];
  begin match d with (* Fails if not well-typed *)
    | SectionLocalAssum ty -> Global.push_named_assum (id,ty)
    | SectionLocalDef c -> Global.push_named_def (id,c)
  end;
  Nametab.push_local sp (VarRef sp);
  vartab := let (m,l) = !vartab in (Spmap.add sp vd m, sp::l)

let (in_variable, out_variable) =
  let od = {
    cache_function = cache_variable;
    load_function = (fun _ -> ());
    open_function = (fun _ -> ());
    export_function = (fun x -> Some x) }
  in
  declare_object ("VARIABLE", od)

let declare_variable id obj =
  let sp = add_leaf id CCI (in_variable (id,obj)) in
  if is_implicit_args() then declare_var_implicits sp;
  sp

(* Parameters. *)

let cache_parameter (sp,c) =
  if Nametab.exists_cci sp then
    errorlabstrm "cache_parameter"
      [< pr_id (basename sp); 'sTR " already exists" >];
  Global.add_parameter sp c (current_section_context ());
  Nametab.push sp (ConstRef sp)

let load_parameter _ = ()

let open_parameter (sp,_) = ()

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

(* Constants. *)

type constant_declaration_type =
  | ConstantEntry  of constant_entry
  | ConstantRecipe of Cooking.recipe

type opacity = bool

type constant_declaration = constant_declaration_type * strength * opacity

let csttab = ref (Spmap.empty : strength Spmap.t)

let _ = Summary.declare_summary "CONSTANT"
	  { Summary.freeze_function = (fun () -> !csttab);
	    Summary.unfreeze_function = (fun ft -> csttab := ft);
	    Summary.init_function = (fun () -> csttab := Spmap.empty);
	    Summary.survive_section = false }

let cache_constant (sp,(cdt,stre,op)) =
  if Nametab.exists_cci sp then
    errorlabstrm "cache_constant"
      [< pr_id (basename sp); 'sTR " already exists" >] ;
  let sc = current_section_context() in
  begin match cdt with 
    | ConstantEntry ce -> Global.add_constant sp ce sc
    | ConstantRecipe r -> Global.add_discharged_constant sp r sc
  end;
  Nametab.push sp (ConstRef sp);
  if op then Global.set_opaque sp;
  csttab := Spmap.add sp stre !csttab

let load_constant (sp,(ce,stre,op)) =
  csttab := Spmap.add sp stre !csttab

let open_constant (sp,_) = ()

let export_constant x = Some x

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
	   const_entry_type = option_app hcons1_constr ce.const_entry_type },
	 stre)
  | cd -> cd

let declare_constant id cd =
  (* let cd = hcons_constant_declaration cd in *)
  let sp = add_leaf id CCI (in_constant cd) in
  if is_implicit_args() then declare_constant_implicits sp;
  sp

(* Inductives. *)


let inductive_names sp mie =
  let names, _ = 
    List.fold_left
      (fun (names, n) ind ->
	 let indsp = (sp,n) in
	 let names, _ =
	   List.fold_left
	     (fun (names, p) id ->
		let sp = Names.make_path (dirpath sp) id CCI in
		((sp, ConstructRef (indsp,p)) :: names, p+1))
	     (names, 1) ind.mind_entry_consnames in
	 let sp = Names.make_path (dirpath sp) ind.mind_entry_typename CCI in
	 ((sp, IndRef indsp) :: names, n+1))
      ([], 0) mie.mind_entry_inds
  in names

let check_exists_inductive (sp,_) =
  if Nametab.exists_cci sp then
    errorlabstrm "cache_inductive"
      [< pr_id (basename sp); 'sTR " already exists" >]

let cache_inductive (sp,mie) =
  let names = inductive_names sp mie in
  List.iter check_exists_inductive names;
  Global.add_mind sp mie (current_section_context ());
  List.iter (fun (sp, ref) -> Nametab.push sp ref) names

let load_inductive _ = ()

let open_inductive (sp,mie) = ()

let export_inductive x = Some x

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
  let sp = add_leaf id CCI (in_inductive mie) in
  if is_implicit_args() then declare_mib_implicits sp;
  sp


(*s Test and access functions. *)

let is_constant sp = 
  try let _ = Global.lookup_constant sp in true with Not_found -> false

let constant_strength sp = Spmap.find sp !csttab

let constant_or_parameter_strength sp =
  try constant_strength sp with Not_found -> NeverDischarge

let get_variable sp = 
  let (id,(_,str,sticky)) = Spmap.find sp (fst !vartab) in
  let (c,ty) = Global.lookup_named id in
  ((id,c,ty),str,sticky)

let variable_strength sp =
  let _,(_,str,_) = Spmap.find sp (fst !vartab) in str

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

let rec occur_section_variable sp = function
  | (_,sp')::_ when sp = sp' -> true
  | _::l -> occur_section_variable sp l
  | [] -> false

let rec quantify_extra_hyps c = function
  | (sp,None,t)::hyps ->
      mkNamedLambda (basename sp) t (quantify_extra_hyps c hyps)
  (* Bugg� car id n'appara�t pas dans les instances des constantes dans c *)
  (* et id n'est donc pas substitu� dans ces constantes *)
  | (sp,Some b,t)::hyps ->
      mkNamedLetIn (basename sp) b t (quantify_extra_hyps c hyps)
  | [] -> c

let find_common_hyps_then_abstract c hyps' hyps =
  let rec find = function
    | (sp,_,_) :: hyps when occur_section_variable sp hyps' -> find hyps
    | hyps -> quantify_extra_hyps c hyps in
  find (List.rev hyps)

let section_variable_paths () = snd !vartab

let find_section_variable id =
  let l =
    Spmap.fold
      (fun sp (id',_) hyps -> if id=id' then sp::hyps else hyps)
      (fst !vartab) [] in
  match l with
    | [] -> raise Not_found
    | [sp] -> sp
    | _ -> error "Arghh, you blasted me with several variables of same name"

let last_section_hyps dir =
  List.fold_right
    (fun sp hyps -> if dirpath sp = dir then basename sp :: hyps else hyps)
    (snd !vartab) []

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
    | (sp,None,_ as d)::hyps ->
	if List.mem_assoc (basename sp) hyps0 then peel (n-1) acc hyps
	else peel (n-1) (args.(n)::acc) hyps
    | (_,Some _,_)::hyps -> peel n acc hyps
    | [] -> Array.of_list acc
  in peel (na-1) [] hyps

let constr_of_reference _ _ ref =
if Options.immediate_discharge then
  match ref with
    | VarRef sp -> mkVar (basename sp)
    | ConstRef sp -> mkConst (sp,[||])
    | ConstructRef sp -> mkMutConstruct (sp,[||])
    | IndRef sp -> mkMutInd (sp,[||])
else
  let hyps = context_of_global_reference ref in
  let hyps0 = current_section_context () in
  let args = instance_from_section_context hyps in
  let body = match ref with
    | VarRef sp -> mkVar (basename sp)
    | ConstRef sp -> mkConst (sp,Array.of_list args)
    | ConstructRef sp -> mkMutConstruct (sp,Array.of_list args)
    | IndRef sp -> mkMutInd (sp,Array.of_list args)
  in
  find_common_hyps_then_abstract body hyps0 hyps

let construct_absolute_reference env sp =
  constr_of_reference Evd.empty env (Nametab.absolute_reference sp)

let construct_qualified_reference env qid =
  let ref = Nametab.locate qid in
  constr_of_reference Evd.empty env ref

let construct_reference env kind id =
  try
    let ref = Nametab.sp_of_id kind id in
    constr_of_reference Evd.empty env ref
  with Not_found ->
    mkVar (let _ = Environ.lookup_named id env in id)

let global_qualified_reference qid =
  construct_qualified_reference (Global.env()) qid

let global_absolute_reference sp = 
  construct_absolute_reference (Global.env()) sp

let global_reference_in_absolute_module dir id = 
  constr_of_reference Evd.empty (Global.env())
    (Nametab.locate_in_absolute_module dir id)

let global_reference kind id = 
  construct_reference (Global.env()) kind id

let dirpath_of_global = function
  | VarRef sp -> dirpath sp
  | ConstRef sp -> dirpath sp
  | IndRef (sp,_) -> dirpath sp
  | ConstructRef ((sp,_),_) -> dirpath sp

let is_global id =
  try 
    let osp = Nametab.locate (make_qualid [] id) in
    list_prefix_of (dirpath_of_global osp) (Lib.cwd())
  with Not_found -> 
    false

let path_of_constructor_path ((sp,tyi),ind) =
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

(* Util *)
let instantiate_inductive_section_params t ind =
  if Options.immediate_discharge then 
  let sign = section_hyps (IndRef ind) in
  let rec inst s ctxt t =
    let k = kind_of_term t in
    match (ctxt,k) with
    | (sp,true)::ctxt, IsLambda(_,_,t) ->
	inst ((mkVar (basename sp))::s) ctxt t
    | (sp,false)::ctxt, IsLetIn(_,_,_,t) -> 
	inst ((mkVar (basename sp))::s) ctxt t
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

let declare_one_elimination mispec =
  let mindstr = string_of_id (mis_typename mispec) in
  let declare na c =
    (* Hack to get const_hyps right in the declaration *)
    let c = instantiate_inductive_section_params c (fst (mis_inductive mispec))
    in
    let _ = declare_constant (id_of_string na)
      (ConstantEntry { const_entry_body = c; const_entry_type = None }, 
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

let lookup_eliminator env path s =
  let dir, base,k = repr_path path in
  let id = id_of_string ((string_of_id base)^(elimination_suffix s)) in
  (* Try first to get an eliminator defined in the same section as the *)
  (* inductive type *)
  try construct_absolute_reference env (Names.make_path dir id k)
  with Not_found ->
  (* Then try to get a user-defined eliminator in some other places *)
  (* using short name (e.g. for "eq_rec") *)
  construct_reference env (kind_of_path path) id
  
