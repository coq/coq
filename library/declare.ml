
(* $Id$ *)

open Util
open Names
open Generic
open Term
open Sign
open Constant
open Inductive
open Reduction
open Libobject
open Lib
open Impargs
open Indrec

type strength = 
  | DischargeAt of section_path 
  | NeverDischarge

(* Variables. *)

let cache_variable (_,obj) = 
  Global.push_var obj

let load_variable _ = 
  anomaly "we shouldn't load a variable"

let open_variable _ = 
  anomaly "we shouldn't open a variable"

let specification_variable _ = 
  anomaly "we shouldn't extract the specification of a variable"

let (in_variable, out_variable) =
  let od = {
    cache_function = cache_variable;
    load_function = load_variable;
    open_function = open_variable;
    specification_function = specification_variable } in
  declare_object ("VARIABLE", od)

let declare_variable id c =
  let obj = (id,c) in
  Global.push_var obj;
  let _ = add_leaf id CCI (in_variable obj) in
  ()

(* Parameters. *)

let cache_parameter (sp,c) =
  Global.add_parameter sp c;
  Nametab.push (basename sp) sp

let open_parameter (sp,_) =
  Nametab.push (basename sp) sp

let specification_parameter obj = obj

let (in_parameter, out_parameter) =
  let od = {
    cache_function = cache_parameter;
    load_function = (fun _ -> ());
    open_function = open_parameter;
    specification_function = specification_parameter } in
  declare_object ("PARAMETER", od)

let declare_parameter id c =
  let sp = add_leaf id CCI (in_parameter c) in
  Global.add_parameter sp c;
  Nametab.push (basename sp) sp
 
(* Constants. *)

let cache_constant (sp,ce) =
  Global.add_constant sp ce;
  Nametab.push (basename sp) sp;
  declare_constant_implicits sp

let open_constant (sp,_) =
  Nametab.push (basename sp) sp;
  declare_constant_implicits sp

let specification_constant obj = obj

let (in_constant, out_constant) =
  let od = {
    cache_function = cache_constant;
    load_function = (fun _ -> ());
    open_function = open_constant;
    specification_function = specification_constant } in
  declare_object ("CONSTANT", od)

let declare_constant id ce =
  let sp = add_leaf id CCI (in_constant ce) in
  Global.add_constant sp ce;
  Nametab.push (basename sp) sp;
  declare_constant_implicits sp
 
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

let open_inductive (sp,mie) =
  push_inductive_names sp mie;
  declare_inductive_implicits sp

let specification_inductive obj = obj

let (in_inductive, out_inductive) =
  let od = {
    cache_function = cache_inductive;
    load_function = (fun _ -> ());
    open_function = open_inductive;
    specification_function = specification_inductive } in
  declare_object ("INDUCTIVE", od)

let declare_mind mie =
  let id = match mie.mind_entry_inds with
    | (id,_,_,_)::_ -> id
    | [] -> anomaly "cannot declare an empty list of inductives"
  in
  let sp = add_leaf id CCI (in_inductive mie) in
  Global.add_mind sp mie;
  push_inductive_names sp mie;
  declare_inductive_implicits sp

(* Syntax constants. *)

let syntax_table = ref (Idmap.empty : constr Idmap.t)

let _ = Summary.declare_summary
	  "SYNTAXCONSTANT"
	  { Summary.freeze_function = (fun () -> !syntax_table);
	    Summary.unfreeze_function = (fun ft -> syntax_table := ft);
	    Summary.init_function = (fun () -> syntax_table := Idmap.empty) }

let add_syntax_constant id c =
  syntax_table := Idmap.add id c !syntax_table

let cache_syntax_constant (sp,c) = 
  add_syntax_constant (basename sp) c;
  Nametab.push (basename sp) sp

let open_syntax_constant (sp,_) =
  Nametab.push (basename sp) sp

let (in_syntax_constant, out_syntax_constant) =
  let od = {
    cache_function = cache_syntax_constant;
    load_function = (fun _ -> ());
    open_function = open_syntax_constant;
    specification_function = (fun x -> x) } in
  declare_object ("SYNTAXCONSTANT", od)

let declare_syntax_constant id c =
  let sp = add_leaf id CCI (in_syntax_constant c) in
  add_syntax_constant id c;
  Nametab.push (basename sp) sp

let out_syntax_constant id = Idmap.find id !syntax_table

(* Test and access functions. *)

let is_constant sp = failwith "TODO"
let constant_strength sp = failwith "TODO"

let is_variable id = failwith "TODO"
let out_variable sp = failwith "TODO"
let variable_strength id = failwith "TODO"

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

let global_operator sp id =
  try
    let cb = Global.lookup_constant sp in Const sp, cb.const_hyps
  with Not_found -> 
    let mib = Global.lookup_mind sp in
    mind_oper_of_id sp id mib, mib.mind_hyps

let global_reference kind id =
  let sp = Nametab.sp_of_id kind id in
  let (oper,_) = global_operator sp id in
  let hyps = get_globals (Global.context ()) in
  let ids = ids_of_sign hyps in
  DOPN(oper, Array.of_list (List.map (fun id -> VAR id) ids))

let global_reference_imps kind id =
  let c = global_reference kind id in
  match c with
    | DOPN (Const sp,_) -> 
	c, list_of_implicits (constant_implicits sp)
    | DOPN (MutInd (sp,i),_) -> 
	c, list_of_implicits (inductive_implicits (sp,i))
    | DOPN (MutConstruct ((sp,i),j),_) ->
	c, list_of_implicits (constructor_implicits ((sp,i),j))
    | _ -> assert false

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

let declare_eliminations sp =
  let env = Global.unsafe_env () in
  let sigma = Evd.empty in
  let mindid = basename sp in
  let mind = global_reference (kind_of_path sp) mindid in
  let redmind = minductype_spec env sigma mind in
  let mindstr = string_of_id mindid in
  let declare na c =
    declare_constant (id_of_string na) 
      { const_entry_body = c; const_entry_type = None } in
  let mispec = Global.lookup_mind_specif redmind in 
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

      
