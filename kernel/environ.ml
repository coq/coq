(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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

type key = (bool*int) option ref 
type constant_key = constant_body * key
 
type engagement = ImpredicativeSet

type globals = {
  env_constants : constant_key KNmap.t;
  env_inductives : mutual_inductive_body KNmap.t;
  env_modules : module_body MPmap.t;
  env_modtypes : module_type_body KNmap.t }

type stratification = {
  env_universes : universes;
  env_engagement : engagement option
}

type 'a val_kind =   
  | VKvalue of values
  | VKaxiom of 'a
  | VKdef of constr * env

and 'a lazy_val = 'a val_kind ref

and env = {
  env_globals       : globals;
  env_named_context : named_context;
  env_named_val     : (identifier * (identifier lazy_val)) list;
  env_rel_context   : rel_context;
  env_rel_val       : inv_rel_key lazy_val list;
  env_nb_rel        : int;
  env_stratification : stratification }

let empty_env = { 
  env_globals = {
    env_constants = KNmap.empty;
    env_inductives = KNmap.empty;
    env_modules = MPmap.empty;
    env_modtypes = KNmap.empty };
  env_named_context = empty_named_context;
  env_named_val = [];
  env_rel_context = empty_rel_context;
  env_rel_val = [];
  env_nb_rel = 0;
  env_stratification = {
    env_universes = initial_universes;
    env_engagement = None } }



let engagement env = env.env_stratification.env_engagement
let universes env = env.env_stratification.env_universes
let named_context env = env.env_named_context
let rel_context env = env.env_rel_context

let empty_context env = 
  env.env_rel_context = empty_rel_context 
  && env.env_named_context = empty_named_context

exception NotEvaluated 
exception AllReadyEvaluated

(* Rel context *)
let lookup_rel n env =
  Sign.lookup_rel n env.env_rel_context

let evaluable_rel n env =
  try
    match lookup_rel n env with
        (_,Some _,_) -> true
      | _ -> false
  with Not_found -> 
    false

let nb_rel env = env.env_nb_rel

let push_rel d env =
  let _,body,_ = d in
  let rval =
    match body with
    | None -> ref (VKaxiom env.env_nb_rel)
    | Some c -> ref (VKdef(c,env))
  in     
  { env with
    env_rel_context = add_rel_decl d env.env_rel_context;
    env_rel_val = rval :: env.env_rel_val;
    env_nb_rel = env.env_nb_rel + 1 }
 

let push_rel_context ctxt x = Sign.fold_rel_context push_rel ctxt ~init:x
    
let push_rec_types (lna,typarray,_) env =
  let ctxt =
    array_map2_i
      (fun i na t -> (na, None, type_app (lift i) t)) lna typarray in
  Array.fold_left (fun e assum -> push_rel assum e) env ctxt
    
let reset_rel_context env =
  { env with
    env_rel_context = empty_rel_context;
    env_rel_val = [];
    env_nb_rel = 0 }

let fold_rel_context f env ~init =
  snd (Sign.fold_rel_context
	 (fun d (env,e) -> (push_rel d env, f env d e))
         (rel_context env) ~init:(reset_rel_context env,init))
    
(* Abstract machine rel values *)
type relval = int lazy_val
      
let kind_of_rel r = !r
    
let set_relval r v =
  match !r with
  | VKvalue _ -> raise AllReadyEvaluated
  | _ -> r := VKvalue v
	
let lookup_relval n env =
  try List.nth env.env_rel_val (n - 1)
  with _ -> raise Not_found
      
(* Named context *)
let lookup_named id env =
  Sign.lookup_named id env.env_named_context
    

    
(* A local const is evaluable if it is defined  *)
let evaluable_named id env =
  try 
    match lookup_named id env with
      (_,Some _,_) -> true
    | _ -> false
  with Not_found -> 
    false
      
let push_named d env = 
  let id,body,_ = d in
  let rval =
    match body with
    | None -> ref (VKaxiom id)
    | Some c -> ref (VKdef(c,env))
  in
  { env with  
    env_named_context = Sign.add_named_decl d env.env_named_context;
    env_named_val =  (id,rval):: env.env_named_val }

let reset_context env =
  { env with
    env_named_context = empty_named_context;
    env_named_val = [];
    env_rel_context = empty_rel_context;
    env_rel_val = [];
    env_nb_rel = 0 }

let reset_with_named_context ctxt env =
  Sign.fold_named_context push_named ctxt ~init:(reset_context env)
    
let fold_named_context f env ~init =
  snd (Sign.fold_named_context
	 (fun d (env,e) -> (push_named d env, f env d e))
         (named_context env) ~init:(reset_context env,init))
    
let fold_named_context_reverse f ~init env =
  Sign.fold_named_context_reverse f ~init:init (named_context env) 
    
(* Abstract machine values of local vars referred by names *)
type namedval = identifier lazy_val

let kind_of_named r = !r

let set_namedval r v =
  match !r with
  | VKvalue _ -> raise AllReadyEvaluated
  | _ -> r := VKvalue v
	
let lookup_namedval id env =
  snd (List.find (fun (id',_) -> id = id') env.env_named_val)
  
(* Global constants *)

let notevaluated = None
    
let constant_key_pos (cb,r) =
  match !r with
  | None -> raise NotEvaluated
  | Some key -> key

let constant_key_body = fst 

let set_pos_constant (cb,r) bpos =
  if !r = notevaluated then r := Some bpos 
  else raise AllReadyEvaluated

let lookup_constant_key kn env =
  KNmap.find kn env.env_globals.env_constants

let lookup_constant kn env = constant_key_body (lookup_constant_key kn env)

let add_constant kn cs env =
  let new_constants = 
    KNmap.add kn (cs,ref notevaluated) env.env_globals.env_constants in
  let new_globals = 
    { env.env_globals with 
	env_constants = new_constants } in 
  { env with env_globals = new_globals }

(* constant_type gives the type of a constant *)
let constant_type env kn =
  let cb = lookup_constant kn env in
  cb.const_type  

type const_evaluation_result = NoBody | Opaque

exception NotEvaluableConst of const_evaluation_result

let constant_value env kn =
  let cb = lookup_constant kn env in
  if cb.const_opaque then raise (NotEvaluableConst Opaque);
  match cb.const_body with
    | Some l_body -> Declarations.force l_body
    | None -> raise (NotEvaluableConst NoBody)

let constant_opt_value env cst =
  try Some (constant_value env cst)
  with NotEvaluableConst _ -> None

(* A global const is evaluable if it is defined and not opaque *)
let evaluable_constant cst env =
  try let _  = constant_value env cst in true
  with Not_found | NotEvaluableConst _ -> false

(* Mutual Inductives *)
let lookup_mind kn env =
  KNmap.find kn env.env_globals.env_inductives

let add_mind kn mib env =
  let new_inds = KNmap.add kn mib env.env_globals.env_inductives in
  let new_globals = 
    { env.env_globals with 
	env_inductives = new_inds } in
  { env with env_globals = new_globals }

(* Universe constraints *)
let set_universes g env =
  if env.env_stratification.env_universes == g then env
  else
    { env with env_stratification = 
      { env.env_stratification with env_universes = g } }

let add_constraints c env =
  if c == Constraint.empty then 
    env 
  else
    let s = env.env_stratification in
    { env with env_stratification = 
      { s with env_universes = merge_constraints c s.env_universes } }

let set_engagement c env = (* Unsafe *)
  { env with env_stratification =
    { env.env_stratification with env_engagement = Some c } }

(* Lookup of section variables *)
let lookup_constant_variables c env =
  let cmap = lookup_constant c env in
  Sign.vars_of_named_context cmap.const_hyps

let lookup_inductive_variables (kn,i) env =
  let mis = lookup_mind kn env in
  Sign.vars_of_named_context mis.mind_hyps

let lookup_constructor_variables (ind,_) env =
  lookup_inductive_variables ind env

(* Returns the list of global variables in a term *)

let vars_of_global env constr =
  match kind_of_term constr with
      Var id -> [id]
    | Const kn -> lookup_constant_variables kn env
    | Ind ind -> lookup_inductive_variables ind env
    | Construct cstr -> lookup_constructor_variables cstr env
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
            (global_vars_set env t) 
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


(* Modules *)

let add_modtype ln mtb env = 
  let new_modtypes = KNmap.add ln mtb env.env_globals.env_modtypes in
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

let lookup_module mp env = 
  MPmap.find mp env.env_globals.env_modules

let lookup_modtype ln env = 
  KNmap.find ln env.env_globals.env_modtypes

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

