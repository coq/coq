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
open Sign
open Univ
open Term
open Declarations

(* The type of environments. *)

type checksum = int

type import = string * checksum

type global = Constant | Inductive

type globals = {
  env_constants : constant_body Spmap.t;
  env_inductives : mutual_inductive_body Spmap.t;
  env_locals : (global * section_path) list;
  env_imports : import list }

type context = {
  env_named_context : named_context;
  env_rel_context : rel_context }

type env = {
  env_context : context;
  env_globals : globals;
  env_universes : universes }

let empty_context = {
  env_named_context = empty_named_context;
  env_rel_context = empty_rel_context }
  
let empty_env = { 
  env_context = empty_context;
  env_globals = {
    env_constants = Spmap.empty;
    env_inductives = Spmap.empty;
    env_locals = [];
    env_imports = [] };
  env_universes = initial_universes }

let universes env = env.env_universes
let context env = env.env_context
let named_context env = env.env_context.env_named_context
let rel_context env = env.env_context.env_rel_context

(* Construction functions. *)

let map_context f env =
  let context = env.env_context in
  { env with
      env_context = {
	context with
	  env_named_context = map_named_context f context.env_named_context ;
	  env_rel_context = map_rel_context f context.env_rel_context } }

let named_context_app f env =
  { env with
      env_context = { env.env_context with
			env_named_context = f env.env_context.env_named_context } }

let change_hyps = named_context_app

let push_named_decl d   = named_context_app (add_named_decl d)
let push_named_def def   = named_context_app (add_named_def def)
let push_named_assum decl = named_context_app (add_named_assum decl)
let pop_named_decl id         = named_context_app (pop_named_decl id)

let rel_context_app f env =
  { env with
      env_context = { env.env_context with
			env_rel_context = f env.env_context.env_rel_context } }

let reset_context env =
  { env with
      env_context = { env_named_context = empty_named_context;
		      env_rel_context = empty_rel_context} }

let fold_named_context f env a =
  snd (Sign.fold_named_context
	 (fun d (env,e) -> (push_named_decl d env, f env d e))
         (named_context env) (reset_context env,a))

let fold_named_context_reverse f a env =
  Sign.fold_named_context_reverse f a (named_context env) 

let process_named_context f env =
  Sign.fold_named_context
    (fun d env -> f env d) (named_context env) (reset_context env)

let process_named_context_both_sides f env =
  fold_named_context_both_sides f (named_context env) (reset_context env)

let push_rel d   = rel_context_app (add_rel_decl d)
let push_rel_def def   = rel_context_app (add_rel_def def)
let push_rel_assum decl = rel_context_app (add_rel_assum decl)
let push_rels ctxt     = rel_context_app (concat_rel_context ctxt)
let push_rels_assum decl env =
  rel_context_app (List.fold_right add_rel_assum decl) env


let push_rel_context_to_named_context env =
  let sign0 = env.env_context.env_named_context in
  let (subst,_,sign) =
  List.fold_right
    (fun (na,c,t) (subst,avoid,sign) ->
       let na = if na = Anonymous then Name(id_of_string"_") else na in
       let id = next_name_away na avoid in
       ((mkVar id)::subst,id::avoid,
	add_named_decl (id,option_app (substl subst) c,type_app (substl subst) t)
	  sign))
    env.env_context.env_rel_context ([],ids_of_named_context sign0,sign0)
  in subst, (named_context_app (fun _ -> sign) env)

let push_rec_types (typarray,names,_) env =
  let vect_lift_type = Array.mapi (fun i t -> lift i t) in
  let nlara = 
    List.combine (List.rev names) (Array.to_list (vect_lift_type typarray)) in
  List.fold_left (fun env nvar -> push_rel_assum nvar env) env nlara

let reset_rel_context env =
  { env with
      env_context = { env_named_context = env.env_context.env_named_context;
		      env_rel_context = empty_rel_context} }

let fold_rel_context f env a =
  snd (List.fold_right
	 (fun d (env,e) -> (push_rel d env, f env d e))
         (rel_context env) (reset_rel_context env,a))

let process_rel_context f env =
  List.fold_right (fun d env -> f env d)
    (rel_context env) (reset_rel_context env)

let instantiate_named_context  = instantiate_sign

let ids_of_context env = 
  (ids_of_rel_context env.env_context.env_rel_context)
  @ (ids_of_named_context env.env_context.env_named_context)

let names_of_rel_context env =
  names_of_rel_context env.env_context.env_rel_context

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

let meta_ctr=ref 0;;

let new_meta ()=incr meta_ctr;!meta_ctr;;

(* Access functions. *)
  
let lookup_named_type id env =
  lookup_id_type id env.env_context.env_named_context

let lookup_named_value id env =
  lookup_id_value id env.env_context.env_named_context

let lookup_named id env = lookup_id id env.env_context.env_named_context

let lookup_rel_type n env =
  Sign.lookup_rel_type n env.env_context.env_rel_context

let lookup_rel_value n env =
  Sign.lookup_rel_value n env.env_context.env_rel_context

let lookup_constant sp env =
  Spmap.find sp env.env_globals.env_constants

let lookup_mind sp env =
  Spmap.find sp env.env_globals.env_inductives

(* First character of a constr *)

let lowercase_first_char id = String.lowercase (first_char id)

(* id_of_global gives the name of the given sort oper *)
let sp_of_global env = function
  | VarRef sp -> sp
  | ConstRef sp -> sp
  | IndRef (sp,tyi) -> 
      (* Does not work with extracted inductive types when the first 
	 inductive is logic : if tyi=0 then basename sp else *)
      let mib = lookup_mind sp env in
      let mip = mind_nth_type_packet mib tyi in
      make_path (dirpath sp) mip.mind_typename CCI
  | ConstructRef ((sp,tyi),i) ->
      let mib = lookup_mind sp env in
      let mip = mind_nth_type_packet mib tyi in
      assert (i <= Array.length mip.mind_consnames && i > 0);
      make_path (dirpath sp) mip.mind_consnames.(i-1) CCI

let id_of_global env ref = basename (sp_of_global env ref)

let hdchar env c = 
  let rec hdrec k c =
    match kind_of_term c with
    | IsProd (_,_,c)       -> hdrec (k+1) c
    | IsLambda (_,_,c)     -> hdrec (k+1) c
    | IsLetIn (_,_,_,c)    -> hdrec (k+1) c
    | IsCast (c,_)         -> hdrec k c
    | IsApp (f,l)         -> hdrec k f
    | IsConst (sp,_)       ->
	let c = lowercase_first_char (basename sp) in
	if c = "?" then "y" else c
    | IsMutInd ((sp,i) as x,_) ->
	if i=0 then 
	  lowercase_first_char (basename sp)
	else 
	  lowercase_first_char (id_of_global env (IndRef x))
    | IsMutConstruct ((sp,i) as x,_) ->
	lowercase_first_char (id_of_global env (ConstructRef x))
    | IsVar id  -> lowercase_first_char id
    | IsSort s -> sort_hdchar s
    | IsRel n ->
	(if n<=k then "p" (* the initial term is flexible product/function *)
	 else
	   try match lookup_rel_type (n-k) env with
	     | Name id,_ -> lowercase_first_char id
	     | Anonymous,t -> hdrec 0 (lift (n-k) (body_of_type t))
	   with Not_found -> "y")
    | IsFix ((_,i),(_,ln,_)) -> 
	let id = match List.nth ln i with Name id -> id | _ -> assert false in
	lowercase_first_char id
    | IsCoFix (i,(_,ln,_)) -> 
	let id = match List.nth ln i with Name id -> id | _ -> assert false in
	lowercase_first_char id
    | IsMeta _|IsEvar _|IsMutCase (_, _, _, _) -> "y"
  in 
  hdrec 0 c

let id_of_name_using_hdchar env a = function
  | Anonymous -> id_of_string (hdchar env a) 
  | Name id   -> id

let named_hd env a = function
  | Anonymous -> Name (id_of_string (hdchar env a)) 
  | x         -> x

let named_hd_type env a = named_hd env (body_of_type a)

let prod_name   env (n,a,b) = mkProd (named_hd_type env a n, a, b)
let lambda_name env (n,a,b) = mkLambda (named_hd_type env a n, a, b)

let prod_create   env (a,b) = mkProd (named_hd_type env a Anonymous, a, b)
let lambda_create env (a,b) =  mkLambda (named_hd_type env a Anonymous, a, b)

let name_assumption env (na,c,t) =
  match c with
    | None      -> (named_hd_type env t na, None, t)
    | Some body -> (named_hd env body na, c, t)

let mkProd_or_LetIn_name env b d = mkProd_or_LetIn (name_assumption env d) b 
let mkLambda_or_LetIn_name env b d = mkLambda_or_LetIn (name_assumption env d)b

let name_context env hyps =
  snd
    (List.fold_left
       (fun (env,hyps) d -> 
	  let d' = name_assumption env d in (push_rel d' env, d' :: hyps))
       (env,[]) (List.rev hyps))

let it_mkProd_wo_LetIn   = List.fold_left (fun c d -> mkProd_wo_LetIn d c)
let it_mkProd_or_LetIn   = List.fold_left (fun c d -> mkProd_or_LetIn d c)
let it_mkLambda_or_LetIn = List.fold_left (fun c d -> mkLambda_or_LetIn d c)

let it_mkProd_or_LetIn_name env b hyps =
  it_mkProd_or_LetIn b (name_context env hyps)

let it_mkLambda_or_LetIn_name env b hyps =
  it_mkLambda_or_LetIn b (name_context env hyps)

let it_mkNamedProd_or_LetIn = it_named_context_quantifier mkNamedProd_or_LetIn
let it_mkNamedLambda_or_LetIn = it_named_context_quantifier mkNamedLambda_or_LetIn

let it_mkNamedProd_wo_LetIn = it_named_context_quantifier mkNamedProd_wo_LetIn

let make_all_name_different env =
  let avoid = ref (ids_of_named_context (named_context env)) in
  process_rel_context
    (fun newenv (na,c,t) -> 
       let id = next_name_away na !avoid in
       avoid := id::!avoid;
       push_rel (Name id,c,t) newenv)
    env

(* Constants *)
let defined_constant env sp = is_defined (lookup_constant sp env)

let opaque_constant env sp = is_opaque (lookup_constant sp env)

(* A global const is evaluable if it is defined and not opaque *)
let evaluable_constant env sp =
  try 
    defined_constant env sp && not (opaque_constant env sp)
  with Not_found -> 
    false

(* A local const is evaluable if it is defined and not opaque *)
let evaluable_named_decl env id =
  try 
    lookup_named_value id env <> None
  with Not_found -> 
    false

let evaluable_rel_decl env n =
  try 
    lookup_rel_value n env <> None
  with Not_found -> 
    false

(*s Opaque / Transparent switching *)

let set_opaque env sp =
  let cb = lookup_constant sp env in
  cb.const_opaque <- true

let set_transparent env sp =
  let cb = lookup_constant sp env in
  cb.const_opaque <- false

(*s Modules (i.e. compiled environments). *)

type compiled_env = {
  cenv_id : string;
  cenv_stamp : checksum;
  cenv_needed : import list;
  cenv_constants : (section_path * constant_body) list;
  cenv_inductives : (section_path * mutual_inductive_body) list }

let exported_objects env =
  let gl = env.env_globals in
  let separate (cst,ind) = function
    | (Constant,sp) -> (sp,Spmap.find sp gl.env_constants)::cst,ind
    | (Inductive,sp) -> cst,(sp,Spmap.find sp gl.env_inductives)::ind
  in
  List.fold_left separate ([],[]) gl.env_locals

let export env id = 
  let (cst,ind) = exported_objects env in
  { cenv_id = id;
    cenv_stamp = 0;
    cenv_needed = env.env_globals.env_imports;
    cenv_constants = cst;
    cenv_inductives = ind }

let check_imports env needed =
  let imports = env.env_globals.env_imports in
  let check (id,stamp) =
    try
      let actual_stamp = List.assoc id imports in
      if stamp <> actual_stamp then
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
      [< 'sTR "Universe Inconsistency during import of"; 'sPC; pr_sp sp >]

let import cenv env =
  check_imports env cenv.cenv_needed;
  let add_list t = List.fold_left (fun t (sp,x) -> Spmap.add sp x t) t in
  let gl = env.env_globals in
  let new_globals = 
    { env_constants = add_list gl.env_constants cenv.cenv_constants;
      env_inductives = add_list gl.env_inductives cenv.cenv_inductives;
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
  uj_type : types }

type unsafe_type_judgment = { 
  utj_val : constr;
  utj_type : sorts }

(*s Memory use of an environment. *)

open Printf

let mem env =
  let glb = env.env_globals in 
  h 0 [< 'sTR (sprintf "%dk (cst = %dk / ind = %dk / unv = %dk)"
		 (size_kb env) (size_kb glb.env_constants) 
		 (size_kb glb.env_inductives) (size_kb env.env_universes)) >]
