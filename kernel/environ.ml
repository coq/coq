(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

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

type env = {
  env_globals       : globals;
  env_named_context : named_context;
  env_rel_context   : rel_context;
  env_universes     : universes }
  
let empty_env = { 
  env_globals = {
    env_constants = Spmap.empty;
    env_inductives = Spmap.empty;
    env_locals = [];
    env_imports = [] };
  env_named_context = empty_named_context;
  env_rel_context = empty_rel_context;
  env_universes = initial_universes }

let universes env = env.env_universes
let named_context env = env.env_named_context
let rel_context env = env.env_rel_context

(* Access functions. *)

let lookup_rel n env =
  Sign.lookup_rel n env.env_rel_context

let lookup_named id env =
  Sign.lookup_named id env.env_named_context

let lookup_constant sp env =
  Spmap.find sp env.env_globals.env_constants

let lookup_mind sp env =
  Spmap.find sp env.env_globals.env_inductives

(* Construction functions. *)

(* Rel context *)
let rel_context_app f env =
  { env with
      env_rel_context = f env.env_rel_context }

let reset_context env =
  { env with
      env_named_context = empty_named_context;
      env_rel_context = empty_rel_context }

let reset_with_named_context ctxt env =
  { env with
      env_named_context = ctxt;
      env_rel_context = empty_rel_context }

let reset_rel_context env =
  { env with
      env_rel_context = empty_rel_context }

let push_rel d   = rel_context_app (add_rel_decl d)
let push_rel_context ctxt x = fold_rel_context push_rel ctxt ~init:x
let push_rel_assum (id,ty) = push_rel (id,None,ty)

let push_rec_types (lna,typarray,_) env =
  let ctxt =
    array_map2_i (fun i na t -> (na, type_app (lift i) t)) lna typarray in
  Array.fold_left
    (fun e assum -> push_rel_assum assum e) env ctxt

let fold_rel_context f env ~init =
  snd (fold_rel_context
	 (fun d (env,e) -> (push_rel d env, f env d e))
         (rel_context env) ~init:(reset_rel_context env,init))

(* Named context *)
let named_context_app f env =
  { env with
      env_named_context = f env.env_named_context }

let push_named_decl d   = named_context_app (add_named_decl d)
let push_named_assum (id,ty) = push_named_decl (id,None,ty)
let pop_named_decl id         = named_context_app (pop_named_decl id)

let fold_named_context f env ~init =
  snd (Sign.fold_named_context
	 (fun d (env,e) -> (push_named_decl d env, f env d e))
         (named_context env) ~init:(reset_context env,init))

let fold_named_context_reverse f ~init env =
  Sign.fold_named_context_reverse f ~init:init (named_context env) 

(* Universe constraints *)
let set_universes g env =
  if env.env_universes == g then env else { env with env_universes = g }

let add_constraints c env =
  if c == Constraint.empty then 
    env 
  else 
    { env with env_universes = merge_constraints c env.env_universes }

(* Global constants *)
let add_constant sp cb env =
  let _ =
    try
      let _ = lookup_constant sp env in failwith "already declared constant"
    with Not_found -> () in
  let new_constants = Spmap.add sp cb env.env_globals.env_constants in
  let new_locals = (Constant,sp)::env.env_globals.env_locals in
  let new_globals = 
    { env.env_globals with 
	env_constants = new_constants; 
	env_locals = new_locals } in
  { env with env_globals = new_globals }

(* Mutual Inductives *)
let add_mind sp mib env =
  let _ =
    try 
      let _ = lookup_mind sp env in failwith "already defined inductive"
    with Not_found -> () in
  let new_inds = Spmap.add sp mib env.env_globals.env_inductives in
  let new_locals = (Inductive,sp)::env.env_globals.env_locals in
  let new_globals = 
    { env.env_globals with 
	env_inductives = new_inds;
	env_locals = new_locals } in
  { env with env_globals = new_globals }

(* Lookup of section variables *)
let lookup_constant_variables c env =
  let cmap = lookup_constant c env in
  Sign.instance_from_named_context cmap.const_hyps

let lookup_inductive_variables (sp,i) env =
  let mis = lookup_mind sp env in
  Sign.instance_from_named_context mis.mind_hyps

let lookup_constructor_variables (ind,_) env =
  lookup_inductive_variables ind env

(* Returns the list of global variables in a term *)

let vars_of_global env constr =
  match kind_of_term constr with
      Var id -> [id]
    | Const sp ->
        List.map destVar 
          (Array.to_list (lookup_constant_variables sp env))
    | Ind ind ->
        List.map destVar 
          (Array.to_list (lookup_inductive_variables ind env))
    | Construct cstr ->
        List.map destVar 
          (Array.to_list (lookup_constructor_variables cstr env))
    | _ -> []

let global_vars_set env constr = 
  let rec filtrec acc c =
    let vl = vars_of_global env c in
    let acc = List.fold_right Idset.add vl acc in
    fold_constr filtrec acc c
  in 
  filtrec Idset.empty constr

(* [keep_hyps env ids] keeps the part of the section context of [env] which 
   contains the variables of the set [ids], and recursively the variables 
   contained in the types of the needed variables. *)

let keep_hyps env needed =
  let really_needed =
    Sign.fold_named_context_reverse
      (fun need (id,copt,t) ->
        if Idset.mem id need then
          let globc = 
	    match copt with
	      | None -> Idset.empty
	      | Some c -> global_vars_set env c in
	  Idset.union
            (global_vars_set env (body_of_type t)) 
	    (Idset.union globc need)
        else need)
      ~init:needed
      (named_context env) in
  Sign.fold_named_context
    (fun (id,_,_ as d) nsign ->
      if Idset.mem id really_needed then add_named_decl d nsign
      else nsign)
    (named_context env)
    ~init:empty_named_context


(* Constants *)

let opaque_constant env sp = (lookup_constant sp env).const_opaque

(* constant_type gives the type of a constant *)
let constant_type env sp =
  let cb = lookup_constant sp env in
  cb.const_type  

type const_evaluation_result = NoBody | Opaque

exception NotEvaluableConst of const_evaluation_result

let constant_value env sp =
  let cb = lookup_constant sp env in
  if cb.const_opaque then raise (NotEvaluableConst Opaque);
  match cb.const_body with
    | Some body -> body
    | None -> raise (NotEvaluableConst NoBody)

let constant_opt_value env cst =
  try Some (constant_value env cst)
  with NotEvaluableConst _ -> None

(* A global const is evaluable if it is defined and not opaque *)
let evaluable_constant env cst =
  try let _  = constant_value env cst in true
  with Not_found | NotEvaluableConst _ -> false

(* A local const is evaluable if it is defined and not opaque *)
let evaluable_named_decl env id =
  try 
    match lookup_named id env with
        (_,Some _,_) -> true
      | _ -> false
  with Not_found -> 
    false

let evaluable_rel_decl env n =
  try
    match lookup_rel n env with
        (_,Some _,_) -> true
      | _ -> false
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
    error "import_constraints: Universe Inconsistency during import"

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

let make_judge v tj =
  { uj_val = v;
    uj_type = tj }

let j_val j = j.uj_val
let j_type j = j.uj_type

type unsafe_type_judgment = { 
  utj_val : constr;
  utj_type : sorts }

