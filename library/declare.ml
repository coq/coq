
(* $Id$ *)

open Pp
open Util
open Names
open Generic
open Term
open Sign
open Constant
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


(* Variables. *)

type variable_declaration = constr * strength * bool

let vartab = ref (Spmap.empty : (identifier * variable_declaration) Spmap.t)

let _ = Summary.declare_summary "VARIABLE"
	  { Summary.freeze_function = (fun () -> !vartab);
	    Summary.unfreeze_function = (fun ft -> vartab := ft);
	    Summary.init_function = (fun () -> vartab := Spmap.empty) }

let cache_variable (sp,(id,(ty,_,_) as vd)) = 
  Global.push_var (id,ty);
  Nametab.push id sp;
  declare_var_implicits id;
  vartab := Spmap.add sp vd !vartab

let load_variable _ = anomaly "we shouldn't load a variable"

let open_variable _ = anomaly "we shouldn't open a variable"

let specification_variable _ = 
  anomaly "we shouldn't extract the specification of a variable"

let (in_variable, out_variable) =
  let od = {
    cache_function = cache_variable;
    load_function = load_variable;
    open_function = open_variable;
    specification_function = specification_variable } in
  declare_object ("VARIABLE", od)

let declare_variable id ((ty,_,_) as obj) =
  let _ = add_leaf id CCI (in_variable (id,obj)) in
  ()

(* Parameters. *)

let cache_parameter (sp,c) =
  Global.add_parameter sp c;
  Nametab.push (basename sp) sp;
  declare_constant_implicits sp

let open_parameter (sp,_) =
  Nametab.push (basename sp) sp;
  declare_constant_implicits sp

let specification_parameter obj = obj

let (in_parameter, out_parameter) =
  let od = {
    cache_function = cache_parameter;
    load_function = (fun _ -> ());
    open_function = open_parameter;
    specification_function = specification_parameter } 
  in
  declare_object ("PARAMETER", od)

let declare_parameter id c =
  let _ = add_leaf id CCI (in_parameter c) in ()
 
(* Constants. *)

type constant_declaration = constant_entry * strength * bool

let csttab = ref (Spmap.empty : constant_declaration Spmap.t)

let _ = Summary.declare_summary "CONSTANT"
	  { Summary.freeze_function = (fun () -> !vartab);
	    Summary.unfreeze_function = (fun ft -> vartab := ft);
	    Summary.init_function = (fun () -> vartab := Spmap.empty) }

let cache_constant (sp,((ce,_,_) as cd)) =
  Global.add_constant sp ce;
  Nametab.push (basename sp) sp;
  declare_constant_implicits sp;
  csttab := Spmap.add sp cd !csttab

let load_constant (sp,((ce,_,_) as cd)) =
  declare_constant_implicits sp;
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
  let _ = add_leaf id CCI (in_constant cd) in ()

 
(* Inductives. *)

let push_inductive_names sp mie =
  List.iter
    (fun (id,_,cnames,_) ->
       Nametab.push id sp;
       List.iter (fun x -> Nametab.push x sp) cnames)
    mie.mind_entry_inds

let cache_inductive (sp,mie) =
  Global.add_mind sp mie;
  push_inductive_names sp mie;
  declare_inductive_implicits sp

let load_inductive (sp,_) =
  declare_inductive_implicits sp

let open_inductive (sp,mie) =
  push_inductive_names sp mie

let specification_inductive obj = obj

let (in_inductive, out_inductive) =
  let od = {
    cache_function = cache_inductive;
    load_function = (fun _ -> ());
    open_function = open_inductive;
    specification_function = specification_inductive } 
  in
  declare_object ("INDUCTIVE", od)

let declare_mind mie =
  let id = match mie.mind_entry_inds with
    | (id,_,_,_)::_ -> id
    | [] -> anomaly "cannot declare an empty list of inductives"
  in
  let sp = add_leaf id CCI (in_inductive mie) in
  sp


(* Test and access functions. *)

let is_constant sp = 
  try let _ = Global.lookup_constant sp in true with Not_found -> false

let constant_strength sp = 
  let (_,stre,_) = Spmap.find sp !csttab in stre

let is_variable id = 
  let sp = Nametab.sp_of_id CCI id in Spmap.mem sp !vartab
  
let out_variable sp = 
  let (id,(_,str,sticky)) = Spmap.find sp !vartab in
  let (_,ty) = Global.lookup_var id in
  (id,ty,str,sticky)

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
	 MutInd (sp,tyi)
       else
	 first 
	   (fun cj cid -> 
	      if id = cid then 
		MutConstruct((sp,tyi),succ cj) 
	      else raise Not_found) 
	   mip.mind_consnames)
    mib.mind_packets

let construct_operator env sp id =
  try
    let cb = Environ.lookup_constant sp env in Const sp, cb.const_hyps
  with Not_found -> 
    let mib = Environ.lookup_mind sp env in
    mind_oper_of_id sp id mib, mib.mind_hyps

let global_operator sp id = construct_operator (Global.env()) sp id

let construct_reference env kind id =
  let sp = Nametab.sp_of_id kind id in
  try
    let (oper,hyps) = construct_operator env sp id in
    let hyps' = Global.var_context () in
    if not (hyps_inclusion env Evd.empty hyps hyps') then
      error_reference_variables CCI env id;
    let ids = ids_of_sign hyps in
    DOPN(oper, Array.of_list (List.map (fun id -> VAR id) ids))
  with Not_found -> 
    VAR (let _ = Environ.lookup_var id env in id)

let global_reference kind id = construct_reference (Global.env()) kind id

let global_reference_imps kind id =
  let c = global_reference kind id in
  match c with
    | DOPN (Const sp,_) -> 
	c, list_of_implicits (constant_implicits sp)
    | DOPN (MutInd (sp,i),_) -> 
	c, list_of_implicits (inductive_implicits (sp,i))
    | DOPN (MutConstruct ((sp,i),j),_) ->
	c, list_of_implicits (constructor_implicits ((sp,i),j))
    | VAR id ->
	c, implicits_of_var kind id
    | _ -> assert false

let global env id =
  try let _ = lookup_glob id (Environ.context env) in VAR id
  with Not_found -> global_reference CCI id

let is_global id =
  try 
    let osp = Nametab.sp_of_id CCI id in
    list_prefix_of (dirpath osp) (Lib.cwd())
  with Not_found -> 
    false

let mind_path = function
  | DOPN(MutInd (sp,0),_) -> sp
  | DOPN(MutInd (sp,tyi),_) -> 
      let mib = Global.lookup_mind sp in
      let mip = mind_nth_type_packet mib tyi in 
      let (pa,_,k) = repr_path sp in 
      Names.make_path pa (mip.mind_typename) k 
  | DOPN(MutConstruct ((sp,tyi),ind),_) -> 
      let mib = Global.lookup_mind sp in
      let mip = mind_nth_type_packet mib tyi in 
      let (pa,_,k) = repr_path sp in 
      Names.make_path pa (mip.mind_consnames.(ind-1)) k 
  | _ -> invalid_arg "mind_path"

(* Eliminations. *)

let declare_eliminations sp i =
  let oper = MutInd (sp,i) in
  let ids = ids_of_sign (Global.var_context()) in
  let mind = DOPN(oper, Array.of_list (List.map (fun id -> VAR id) ids)) in
  let mispec = Global.lookup_mind_specif mind in 
  let mindstr = string_of_id (mis_typename mispec) in
  let declare na c =
    declare_constant (id_of_string na)
      ({ const_entry_body = c; const_entry_type = None },
       NeverDischarge, false);
    pPNL [< 'sTR na; 'sTR " is defined" >]
  in
  let env = Global.env () in
  let sigma = Evd.empty in
  let elim_scheme = 
    strip_all_casts (mis_make_indrec env sigma [] mispec).(0) in
  let npars = mis_nparams mispec in
  let make_elim s = instanciate_indrec_scheme s npars elim_scheme in
  let kelim = mis_kelim mispec in
  if List.mem prop kelim then
    declare (mindstr^"_ind") (make_elim prop);
  if List.mem spec kelim then
    declare (mindstr^"_rec") (make_elim spec);
  if List.mem types kelim then
    declare (mindstr^"_rect") (make_elim (Type (Univ.new_univ sp)))

      
