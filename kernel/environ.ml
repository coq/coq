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

type compilation_unit_name = dir_path * checksum

type global = Constant | Inductive

type globals = {
  env_constants : constant_body Spmap.t;
  env_inductives : mutual_inductive_body Spmap.t;
  env_locals : (global * section_path) list;
  env_imports : compilation_unit_name list }

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

let push_rec_types (lna,typarray,_) env =
  let ctxt =
    array_map2_i (fun i na t -> (na, type_app (lift i) t)) lna typarray in
  Array.fold_left
    (fun e assum -> push_rel_assum assum e) env ctxt

let push_named_rec_types (lna,typarray,_) env =
  let ctxt =
    array_map2_i
      (fun i na t ->
	 match na with
	   | Name id -> (id, type_app (lift i) t)
	   | Anonymous -> anomaly "Fix declarations must be named")
      lna typarray in
  Array.fold_left
    (fun e assum -> push_named_assum assum e) env ctxt

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


(* Lookup of section variables *)
let lookup_constant_variables c env =
  let cmap = lookup_constant c env in
  Sign.instance_from_section_context cmap.const_hyps

let lookup_inductive_variables (sp,i) env =
  let mis = lookup_mind sp env in
  Sign.instance_from_section_context mis.mind_hyps

let lookup_constructor_variables (ind,_) env =
  lookup_inductive_variables ind env

(* Returns the list of global variables in a term *)

let vars_of_global env constr =
  match kind_of_term constr with
      IsVar id -> [id]
    | IsConst sp ->
        List.map destVar 
          (Array.to_list (lookup_constant_variables sp env))
    | IsMutInd ind ->
        List.map destVar 
          (Array.to_list (lookup_inductive_variables ind env))
    | IsMutConstruct cstr ->
        List.map destVar 
          (Array.to_list (lookup_constructor_variables cstr env))
    | _ -> []

let rec global_varsl env l constr =
  let l = vars_of_global env constr @ l in
  fold_constr (global_varsl env) l constr

let global_vars env = global_varsl env []

let global_vars_decl env = function
  | (_, None, t) -> global_vars env t
  | (_, Some c, t) -> (global_vars env c)@(global_vars env t)

let global_vars_set env constr = 
  let rec filtrec acc c =
    let vl = vars_of_global env c in
    let acc = List.fold_right Idset.add vl acc in
    fold_constr filtrec acc c
  in 
  filtrec Idset.empty constr


exception Occur

let occur_in_global env id constr =
  let vars = vars_of_global env constr in
  if List.mem id vars then raise Occur

let occur_var env s c = 
  let rec occur_rec c =
    occur_in_global env s c;
    iter_constr occur_rec c
  in 
  try occur_rec c; false with Occur -> true

let occur_var_in_decl env hyp (_,c,typ) =
  match c with
    | None -> occur_var env hyp (body_of_type typ)
    | Some body ->
        occur_var env hyp (body_of_type typ) ||
        occur_var env hyp body

(* [keep_hyps sign ids] keeps the part of the signature [sign] which 
   contains the variables of the set [ids], and recursively the variables 
   contained in the types of the needed variables. *)

let rec keep_hyps env needed = function
  | (id,copt,t as d) ::sign when Idset.mem id needed ->
      let globc = 
	match copt with
	  | None -> Idset.empty
	  | Some c -> global_vars_set env c in
      let needed' =
	Idset.union (global_vars_set env (body_of_type t)) 
	  (Idset.union globc needed) in
      d :: (keep_hyps env needed' sign)
  | _::sign -> keep_hyps env needed sign
  | [] -> []

(* This renames bound variables with fresh and distinct names *)
(* in such a way that the printer doe not generate new names  *)
(* and therefore that printed names are the intern names      *)
(* In this way, tactics such as Induction works well          *)

let rec rename_bound_var env l c =
  match kind_of_term c with
  | IsProd (Name s,c1,c2)  ->
      if dependent (mkRel 1) c2 then
        let s' = next_ident_away s (global_vars env c2@l) in
        let env' = push_rel (Name s',None,c1) env in
        mkProd (Name s', c1, rename_bound_var env' (s'::l) c2)
      else 
        let env' = push_rel (Name s,None,c1) env in
	mkProd (Name s, c1, rename_bound_var env' l c2)
  | IsProd (Anonymous,c1,c2) ->
        let env' = push_rel (Anonymous,None,c1) env in
        mkProd (Anonymous, c1, rename_bound_var env' l c2)
  | IsCast (c,t) -> mkCast (rename_bound_var env l c, t)
  | x -> c

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
    | IsConst sp       ->
	let c = lowercase_first_char (basename sp) in
	if c = "?" then "y" else c
    | IsMutInd ((sp,i) as x) ->
	if i=0 then 
	  lowercase_first_char (basename sp)
	else 
	  lowercase_first_char (id_of_global env (IndRef x))
    | IsMutConstruct ((sp,i) as x) ->
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
    | IsFix ((_,i),(lna,_,_)) -> 
	let id = match lna.(i) with Name id -> id | _ -> assert false in
	lowercase_first_char id
    | IsCoFix (i,(lna,_,_)) -> 
	let id = match lna.(i) with Name id -> id | _ -> assert false in
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

let opaque_constant env sp = (lookup_constant sp env).const_opaque

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

(*s Modules (i.e. compiled environments). *)

type compiled_env = {
  cenv_stamped_id : compilation_unit_name;
  cenv_needed : compilation_unit_name list;
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
  { cenv_stamped_id = (id,0);
    cenv_needed = env.env_globals.env_imports;
    cenv_constants = cst;
    cenv_inductives = ind }

let check_imports env needed =
  let imports = env.env_globals.env_imports in
  let check (id,stamp) =
    try
      let actual_stamp = List.assoc id imports in
      if stamp <> actual_stamp then
	error ("Inconsistent assumptions over module " ^(string_of_dirpath id))
    with Not_found -> 
      error ("Reference to unknown module " ^ (string_of_dirpath id))
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
      env_imports = cenv.cenv_stamped_id :: gl.env_imports }
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
