
(* $Id$ *)

open Pp
open System
open Util
open Names
open Sign
open Univ
open Generic
open Term
open Evd
open Constant
open Inductive
open Abstraction

(* The type of environments. *)

type import = string * time_stamp

type global = Constant | Inductive | Abstraction

type globals = {
  env_constants : constant_body Spmap.t;
  env_inductives : mutual_inductive_body Spmap.t;
  env_abstractions : abstraction_body Spmap.t;
  env_locals : (global * section_path) list;
  env_imports : import list }

type 'a unsafe_env = {
  env_context : context;
  env_globals : globals;
  env_sigma : 'a evar_map;
  env_metamap : (int * constr) list;
  env_universes : universes }

let empty_env = { 
  env_context = ENVIRON (([],[]),[]);
  env_globals = {
    env_constants = Spmap.empty;
    env_inductives = Spmap.empty;
    env_abstractions = Spmap.empty;
    env_locals = [];
    env_imports = [] };
  env_sigma = mt_evd;
  env_metamap = [];
  env_universes = initial_universes }

let universes env = env.env_universes
let metamap env = env.env_metamap
let evar_map env = env.env_sigma
let context env = env.env_context

(* Construction functions. *)

let push_var idvar env =
  { env with env_context = add_glob idvar env.env_context }

let push_rel idrel env =
  { env with env_context = add_rel idrel env.env_context }

let set_universes g env =
  if env.env_universes == g then env else { env with env_universes = g }

let add_constraints c env =
  if c == Constraint.empty then 
    env 
  else 
    { env with env_universes = merge_constraints c env.env_universes }

let add_constant sp cb env =
  let new_constants = Spmap.add sp cb env.env_globals.env_constants in
  let new_locals = (Constant,sp)::env.env_globals.env_locals in
  let new_globals = 
    { env.env_globals with 
	env_constants = new_constants; 
	env_locals = new_locals } in
  { env with env_globals = new_globals }

let add_mind sp mib env =
  let new_inds = Spmap.add sp mib env.env_globals.env_inductives in
  let new_locals = (Inductive,sp)::env.env_globals.env_locals in
  let new_globals = 
    { env.env_globals with 
	env_inductives = new_inds;
	env_locals = new_locals } in
  { env with env_globals = new_globals }

let add_abstraction sp ab env =
  let new_abs = Spmap.add sp ab env.env_globals.env_abstractions in
  let new_locals = (Abstraction,sp)::env.env_globals.env_locals in
  let new_globals = 
    { env.env_globals with 
	env_abstractions = new_abs;
	env_locals = new_locals } in
  { env with env_globals = new_globals }
  
let new_meta = 
  let meta_ctr = ref 0 in
  fun () -> (incr meta_ctr; !meta_ctr)

(* Access functions. *)
  
let lookup_var id env =
  let (_,var) = lookup_glob id env.env_context in
  (Name id, var)

let lookup_rel n env =
  Sign.lookup_rel n env.env_context

let lookup_constant sp env =
  Spmap.find sp env.env_globals.env_constants

let lookup_mind sp env =
  Spmap.find sp env.env_globals.env_inductives

let lookup_mind_specif i env =
  match i with
    | DOPN (MutInd (sp,tyi), args) ->
	let mib = lookup_mind sp env in
	{ mis_sp = sp; mis_mib = mib; mis_tyi = tyi; mis_args = args;
	  mis_mip = mind_nth_type_packet mib tyi }
    | _ -> invalid_arg "lookup_mind_specif"

let lookup_meta n env =
  List.assoc n env.env_metamap

let lookup_abst sp env =
  Spmap.find sp env.env_globals.env_abstractions

(* First character of a constr *)

let lowercase_first_char id = String.lowercase (first_char id)

(* id_of_global gives the name of the given sort oper *)
let id_of_global env = function
  | Const sp -> 
      basename sp
  | MutInd (sp,tyi) -> 
      (* Does not work with extracted inductive types when the first 
	 inductive is logic : if tyi=0 then basename sp else *)
      let mib = lookup_mind sp env in
      let mip = mind_nth_type_packet mib tyi in
      mip.mind_typename
  | MutConstruct ((sp,tyi),i) ->
      let mib = lookup_mind sp env in
      let mip = mind_nth_type_packet mib tyi in
      assert (i <= Array.length mip.mind_consnames && i > 0);
      mip.mind_consnames.(i-1)
  | _ -> 
      assert false

let hdchar env c = 
  let rec hdrec = function
    | DOP2(Prod,_,DLAM(_,c))     -> hdrec c
    | DOP2(Cast,c,_)             -> hdrec c
    | DOPN(AppL,cl)              -> hdrec (array_hd cl)
    | DOP2(Lambda,_,DLAM(_,c))   -> hdrec c
    | DOPN(Const _,_) as x ->
	let c = lowercase_first_char (basename (path_of_const x)) in
	if c = "?" then "y" else c
    | DOPN(Abst _,_) as x ->
	lowercase_first_char (basename (path_of_abst x))
    | DOPN(MutInd (sp,i) as x,_) ->
	if i=0 then 
	  lowercase_first_char (basename sp)
	else 
	  let na = id_of_global env x in lowercase_first_char na
    | DOPN(MutConstruct(sp,i) as x,_) ->
	let na = id_of_global env x in String.lowercase(List.hd(explode_id na))
    | VAR id  -> lowercase_first_char id
    | DOP0(Sort s) -> sort_hdchar s
    | _ -> "y"
  in 
  hdrec c

let id_of_name_using_hdchar env a = function
  | Anonymous -> id_of_string (hdchar env a) 
  | Name id   -> id

let named_hd env a = function
  | Anonymous -> Name (id_of_string (hdchar env a)) 
  | x         -> x

let prod_name env (n,a,b) = mkProd (named_hd env a n) a b

(* Abstractions. *)

let evaluable_abst env = function
  | DOPN (Abst _,_) -> true
  | _ -> invalid_arg "evaluable_abst"

let translucent_abst env = function
  | DOPN (Abst _,_) -> false
  | _ -> invalid_arg "translucent_abst"

let abst_value env = function
  | DOPN(Abst sp, args) ->
    contract_abstraction (lookup_abst sp env) args
  | _ -> invalid_arg "abst_value"

let defined_constant env = function
  | DOPN (Const sp, _) ->
      Constant.is_defined (lookup_constant sp env)
  | _ -> invalid_arg "defined_constant"

(* A constant is an existential if its name has the existential id prefix *)
let existential_id_prefix = "?"

let is_existential_id id =
  atompart_of_id id = existential_id_prefix

let is_existential_oper = function
  | Const sp -> is_existential_id (basename sp)
  | _ -> false

let is_existential = function
  | DOPN (oper, _) -> is_existential_oper oper
  | _ -> false

let defined_existential env = function
  | DOPN (Const sp, _) -> 
      Evd.is_defined env.env_sigma sp
  | _ -> invalid_arg "defined_existential"

let defined_const env c =
  (defined_constant env c) || 
  ((is_existential c) && (defined_existential env c))

let translucent_const env c =
  (is_existential c) && (defined_existential env c)

(* A const is opaque if it is a non-defined existential or
   a non-existential opaque constant *)

let opaque_constant env = function
  | DOPN (Const sp, _) -> 
      Constant.is_opaque (lookup_constant sp env)
  | _ -> invalid_arg "opaque_constant"

let opaque_const env = function
  | DOPN(Const sp,_) as k ->
      if is_existential k then
        not (defined_existential env k)
      else 
	opaque_constant env k
  | _ -> invalid_arg "opaque_const"

(* A const is evaluable if it is defined and not opaque *)
let evaluable_const env k =
  try 
    defined_const env k && not (opaque_const env k)
  with Not_found -> 
    false

(*s Modules (i.e. compiled environments). *)

type compiled_env = {
  cenv_id : string;
  cenv_stamp : time_stamp;
  cenv_needed : import list;
  cenv_constants : (section_path * constant_body) list;
  cenv_inductives : (section_path * mutual_inductive_body) list;
  cenv_abstractions : (section_path * abstraction_body) list }

let exported_objects env =
  let gl = env.env_globals in
  let separate (cst,ind,abs) = function
    | (Constant,sp) -> (sp,Spmap.find sp gl.env_constants)::cst,ind,abs
    | (Inductive,sp) -> cst,(sp,Spmap.find sp gl.env_inductives)::ind,abs
    | (Abstraction,sp) -> cst,ind,(sp,Spmap.find sp gl.env_abstractions)::abs
  in
  List.fold_left separate ([],[],[]) gl.env_locals

let export env id = 
  let (cst,ind,abs) = exported_objects env in
  { cenv_id = id;
    cenv_stamp = get_time_stamp ();
    cenv_needed = env.env_globals.env_imports;
    cenv_constants = cst;
    cenv_inductives = ind;
    cenv_abstractions = abs }

let check_imports env needed =
  let imports = env.env_globals.env_imports in
  let check (id,stamp) =
    try
      let actual_stamp = List.assoc id imports in
      if compare_time_stamps stamp actual_stamp <> 0 then
	error ("Inconsistent assumptions over module " ^ id)
    with Not_found -> 
      error ("Reference to unknown module " ^ id)
  in
  List.iter check needed

let import_constraints g sp cst =
  try
    merge_constraints cst g
  with UniverseInconsistency ->
    errorlabstrm "import_constraints"
      [< 'sTR "Universe Inconsistency during import of"; 'sPC; print_sp sp >]

let import cenv env =
  check_imports env cenv.cenv_needed;
  let add_list t = List.fold_left (fun t (sp,x) -> Spmap.add sp x t) t in
  let gl = env.env_globals in
  let new_globals = 
    { env_constants = add_list gl.env_constants cenv.cenv_constants;
      env_inductives = add_list gl.env_inductives cenv.cenv_inductives;
      env_abstractions = add_list gl.env_abstractions cenv.cenv_abstractions;
      env_locals = gl.env_locals;
      env_imports = (cenv.cenv_id,cenv.cenv_stamp) :: gl.env_imports }
  in
  let g = universes env in
  let g = List.fold_left 
	    (fun g (sp,cb) -> import_constraints g sp cb.const_constraints) 
	    g cenv.cenv_constants in
  let g = List.fold_left 
	    (fun g (sp,mib) -> import_constraints g sp mib.mind_constraints) 
	    g cenv.cenv_inductives in
  { env with env_globals = new_globals; env_universes = g }

(*s Judgments. *)

type unsafe_judgment = { 
  uj_val : constr;
  uj_type : constr;
  uj_kind : constr }

let cast_of_judgment = function
  | { uj_val = DOP2 (Cast,_,_) as c } -> c
  | { uj_val = c; uj_type = ty } -> mkCast c ty

