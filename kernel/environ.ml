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
open Sign
open Univ
open Term
open Declarations
open Mod_declarations

(* The type of environments. *)

type globals = {
  env_constants : constant_body LNmap.t;
  env_inductives : mutual_inductive_body LNmap.t;
  env_modules : module_body MPmap.t;
  env_modtypes : module_type_body LNmap.t }

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
    env_constants = LNmap.empty;
    env_inductives = LNmap.empty;
    env_modules = MPmap.empty;
    env_modtypes = LNmap.empty };
  env_universes = initial_universes }

let universes env = env.env_universes
(*let context env = env.env_context*)
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
let push_rels ctxt     = rel_context_app (fun older -> concat_rel_context ~newer:ctxt ~older)
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

let add_constant ln cb env =
  let new_constants = LNmap.add ln cb env.env_globals.env_constants in
  let new_globals = 
    { env.env_globals with 
	env_constants = new_constants } in
  { env with env_globals = new_globals }

let add_mind ln mib env =
  let new_inds = LNmap.add ln mib env.env_globals.env_inductives in
  let new_globals = 
    { env.env_globals with 
	env_inductives = new_inds } in
  { env with env_globals = new_globals }

let add_modtype ln mtb env = 
  let new_modtypes = LNmap.add ln mtb env.env_globals.env_modtypes in
  let new_globals = 
    { env.env_globals with 
	env_modtypes = new_modtypes } in
  { env with env_globals = new_globals }

let shallow_add_module mp mb env = 
  let new_mods = MPmap.add mp mb env.env_globals.env_modules in
  let new_globals = 
    { env.env_globals with 
	env_modules = new_mods } in
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

let lookup_constant ln env =
  LNmap.find ln env.env_globals.env_constants

let lookup_mind ln env =
  LNmap.find ln env.env_globals.env_inductives

let lookup_module mp env = 
  MPmap.find mp env.env_globals.env_modules

let lookup_modtype ln env = 
  LNmap.find ln env.env_globals.env_modtypes

(* First character of a constr *)
let lowercase_first_char l = String.lowercase (first_char l)

let id_of_global env = function
  | VarRef id -> id
  | ConstRef ln -> basename ln
  | IndRef (ln,tyi) -> 
      (* Does not work with extracted inductive types when the first 
	 inductive is logic : if tyi=0 then basename sp else *)
      let mib = lookup_mind ln env in
      let mip = mind_nth_type_packet mib tyi in
	ident_of_label mip.mind_typename
  | ConstructRef ((ln,tyi),i) ->
      let mib = lookup_mind ln env in
      let mip = mind_nth_type_packet mib tyi in
	assert (i <= Array.length mip.mind_consnames && i > 0);
	ident_of_label mip.mind_consnames.(i-1)
  | ModRef (MPdot (_,l)) -> ident_of_label l
  | ModRef _ -> anomaly "Environ.id_of_global: ModRef is not mp.l"
  | ModTypeRef ln -> basename ln

let hdchar env c = 
  let rec hdrec k c =
    match kind_of_term c with
    | IsProd (_,_,c)       -> hdrec (k+1) c
    | IsLambda (_,_,c)     -> hdrec (k+1) c
    | IsLetIn (_,_,_,c)    -> hdrec (k+1) c
    | IsCast (c,_)         -> hdrec k c
    | IsApp (f,l)         -> hdrec k f
    | IsConst (ln,_)       ->
	let c = lowercase_first_char (basename ln) in
	if c = "?" then "y" else c
    | IsMutInd ((ln,i) as x,_) ->
	if i=0 then 
	  lowercase_first_char (basename ln)
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
  h 0 (str (sprintf "%dk (cst = %dk / ind = %dk / unv = %dk)"
		 (size_kb env) (size_kb glb.env_constants) 
		 (size_kb glb.env_inductives) (size_kb env.env_universes)) )


