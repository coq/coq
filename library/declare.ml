
(* $Id$ *)

open Pp
open Util
open Names
(* open Generic *)
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

type strength = 
  | DischargeAt of section_path 
  | NeverDischarge

let make_strength = function
  | [] -> NeverDischarge
  | l  -> DischargeAt (sp_of_wd l)

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
  | SectionLocalDecl of constr

type sticky = bool

type variable_declaration = section_variable_entry * strength * sticky

let vartab = ref (Spmap.empty : (identifier * variable_declaration) Spmap.t)

let _ = Summary.declare_summary "VARIABLE"
	  { Summary.freeze_function = (fun () -> !vartab);
	    Summary.unfreeze_function = (fun ft -> vartab := ft);
	    Summary.init_function = (fun () -> vartab := Spmap.empty) }

let cache_variable (sp,((id,(d,_,_) as vd),imps)) =
  begin match d with (* Fails if not well-typed *)
    | SectionLocalDecl ty -> Global.push_var_decl (id,ty)
    | SectionLocalDef c -> Global.push_var_def (id,c)
  end;
  Nametab.push id sp;
  if imps then declare_var_implicits id;
  vartab := Spmap.add sp vd !vartab

let load_variable _ = ()

let open_variable _ = ()

let specification_variable x = x

let (in_variable, _ (* out_variable *) ) =
  let od = {
    cache_function = cache_variable;
    load_function = load_variable;
    open_function = open_variable;
    specification_function = specification_variable } in
  declare_object ("VARIABLE", od)

let declare_variable id obj =
  let _ = add_leaf id CCI (in_variable ((id,obj),is_implicit_args())) in
  ()

(* Parameters. *)

let cache_parameter (sp,(c,imps)) =
  Global.add_parameter sp c;
  Nametab.push (basename sp) sp;
  if imps then declare_constant_implicits sp

let load_parameter (sp,(_,imps)) =
  if imps then declare_constant_implicits sp

let open_parameter (sp,_) =
  Nametab.push (basename sp) sp

let specification_parameter obj = obj

let (in_parameter, out_parameter) =
  let od = {
    cache_function = cache_parameter;
    load_function = load_parameter;
    open_function = open_parameter;
    specification_function = specification_parameter } 
  in
  declare_object ("PARAMETER", od)

let declare_parameter id c =
  let _ = add_leaf id CCI (in_parameter (c,is_implicit_args())) in ()

(* Constants. *)

type constant_declaration = constant_entry * strength

let csttab = ref (Spmap.empty : constant_declaration Spmap.t)

let _ = Summary.declare_summary "CONSTANT"
	  { Summary.freeze_function = (fun () -> !csttab);
	    Summary.unfreeze_function = (fun ft -> csttab := ft);
	    Summary.init_function = (fun () -> csttab := Spmap.empty) }

let cache_constant (sp,((ce,_) as cd,imps)) =
  Global.add_constant sp ce;
  Nametab.push (basename sp) sp;
  if imps then declare_constant_implicits sp;
  csttab := Spmap.add sp cd !csttab

let load_constant (sp,((ce,_) as cd,imps)) =
  if imps then declare_constant_implicits sp;
  csttab := Spmap.add sp cd !csttab

let open_constant (sp,_) =
  Nametab.push (basename sp) sp

let specification_constant obj = obj

let (in_constant, out_constant) =
  let od = {
    cache_function = cache_constant;
    load_function = load_constant;
    open_function = open_constant;
    specification_function = specification_constant } 
  in
  declare_object ("CONSTANT", od)

let declare_constant id cd =
  let _ = add_leaf id CCI (in_constant (cd,is_implicit_args())) in ()

 
(* Inductives. *)

let push_inductive_names sp mie =
  List.iter
    (fun (id,_,cnames,_) ->
       Nametab.push id sp;
       List.iter (fun x -> Nametab.push x sp) cnames)
    mie.mind_entry_inds

let cache_inductive (sp,(mie,imps)) =
  Global.add_mind sp mie;
  push_inductive_names sp mie;
  if imps then declare_inductive_implicits sp

let load_inductive (sp,(_,imps)) =
  if imps then declare_inductive_implicits sp

let open_inductive (sp,(mie,_)) =
  push_inductive_names sp mie

let specification_inductive obj = obj

let (in_inductive, out_inductive) =
  let od = {
    cache_function = cache_inductive;
    load_function = load_inductive;
    open_function = open_inductive;
    specification_function = specification_inductive } 
  in
  declare_object ("INDUCTIVE", od)

let declare_mind mie =
  let id = match mie.mind_entry_inds with
    | (id,_,_,_)::_ -> id
    | [] -> anomaly "cannot declare an empty list of inductives"
  in
  let sp = add_leaf id CCI (in_inductive (mie,is_implicit_args())) in
  sp


(* Test and access functions. *)

let is_constant sp = 
  try let _ = Global.lookup_constant sp in true with Not_found -> false

let constant_strength sp = 
  let (_,stre) = Spmap.find sp !csttab in stre

let constant_or_parameter_strength sp =
  try constant_strength sp with Not_found -> NeverDischarge

let is_variable id = 
  let sp = Nametab.sp_of_id CCI id in Spmap.mem sp !vartab
  
let out_variable sp = 
  let (id,(_,str,sticky)) = Spmap.find sp !vartab in
  let (c,ty) = Global.lookup_var id in
  ((id,c,ty),str,sticky)

let variable_strength id =
  let sp = Nametab.sp_of_id CCI id in 
  let _,(_,str,_) = Spmap.find sp !vartab in
  str

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

let global_sp_operator env sp id =
  try
    let cb = Environ.lookup_constant sp env in ConstRef sp, cb.const_hyps
  with Not_found -> 
    let mib = Environ.lookup_mind sp env in
    mind_oper_of_id sp id mib, mib.mind_hyps

let global_operator kind id =
  let sp = Nametab.sp_of_id kind id in
  global_sp_operator (Global.env()) sp id

let occur_decl env (id,c,t) hyps =
  try
    let (c',t') = Sign.lookup_id id hyps in
    let matching_bodies = match c,c' with
      | None, _ -> true
      | Some c, None -> false
      | Some c, Some c' -> is_conv env Evd.empty c c' in
    let matching_types = 
      is_conv env Evd.empty (body_of_type t) (body_of_type t') in
    matching_types & matching_bodies
  with Not_found -> false

(*
let rec find_common_hyps_then_abstract c env hyps' = function
  | (id,_,_ as d) :: hyps when occur_decl env d hyps' ->
      find_common_hyps_then_abstract c (Environ.push_var d env) hyps' hyps
  | hyps ->
      Environ.it_mkNamedLambda_or_LetIn c hyps

let find_common_hyps_then_abstract c env hyps' hyps =
  find_common_hyps_then_abstract c env hyps' (List.rev hyps)
*)

let find_common_hyps_then_abstract c env hyps' hyps = 
  snd (fold_var_context_both_sides
	 (fun
	    (env,c) (id,_,_ as d) hyps ->
	      if occur_decl env d hyps' then 
		(Environ.push_var d env,c)
	      else
		(env, Environ.it_mkNamedLambda_or_LetIn c hyps))
	 hyps
	 (env,c))

let construct_sp_reference env sp id =
  let (oper,hyps) = global_sp_operator env sp id in
  let hyps0 = Global.var_context () in
  let env0 = Environ.reset_context env in
  let args = List.map mkVar (ids_of_var_context hyps) in
  let body = match oper with
    | ConstRef sp -> mkConst (sp,Array.of_list args)
    | ConstructRef sp -> mkMutConstruct (sp,Array.of_list args)
    | IndRef sp -> mkMutInd (sp,Array.of_list args)
  in
  find_common_hyps_then_abstract body env0 hyps0 hyps

let construct_reference env kind id =
  try
    let sp = Nametab.sp_of_id kind id in
    construct_sp_reference env sp id
  with Not_found -> 
    mkVar (let _ = Environ.lookup_var id env in id)

let global_sp_reference sp id = 
  construct_sp_reference (Global.env()) sp id

let global_reference kind id = 
  construct_reference (Global.env()) kind id

let global_reference_imps kind id =
  let c = global_reference kind id in
  match kind_of_term c with
    | IsConst (sp,_) -> c, list_of_implicits (constant_implicits sp)
    | IsMutInd (isp,_) -> c, list_of_implicits (inductive_implicits isp)
    | IsMutConstruct (csp,_) ->	c,list_of_implicits (constructor_implicits csp)
    | IsVar id -> c, implicits_of_var id
    | _ -> assert false
(*
let global env id =
  try let _ = lookup_glob id (Environ.context env) in mkVar id
  with Not_found -> global_reference CCI id
*)
let is_global id =
  try 
    let osp = Nametab.sp_of_id CCI id in
    list_prefix_of (dirpath osp) (Lib.cwd())
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

(* Eliminations. *)

let eliminations = [ (prop,"_ind") ; (spec,"_rec") ; (types,"_rect") ]

let elimination_suffix = function
  | Type _    -> "_rect"
  | Prop Null -> "_ind"
  | Prop Pos  -> "_rec"

let declare_eliminations sp i =
  let mib = Global.lookup_mind sp in
  let ids = ids_of_var_context mib.mind_hyps in
  if not (list_subset ids (ids_of_var_context (Global.var_context ()))) then
    error ("Declarations of elimination scheme outside the section "^
    "of the inductive definition is not implemented");
  let ctxt = Array.of_list (List.map mkVar ids) in
  let mispec = Global.lookup_mind_specif ((sp,i),ctxt) in 
  let mindstr = string_of_id (mis_typename mispec) in
  let declare na c =
    declare_constant (id_of_string na)
      ({ const_entry_body = Cooked c; const_entry_type = None }, 
       NeverDischarge);
    if Options.is_verbose() then pPNL [< 'sTR na; 'sTR " is defined" >]
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

(* Look up function for the default elimination constant *)

let lookup_eliminator env path s =
  let s = (string_of_id (basename path))^(elimination_suffix s) in
  construct_reference env (kind_of_path path) (id_of_string s)

      
