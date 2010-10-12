open Util
open Names
open Univ
open Term
open Declarations

type globals = {
  env_constants : constant_body Cmap_env.t;
  env_inductives : mutual_inductive_body Mindmap_env.t;
  env_inductives_eq : kernel_name  KNmap.t;
  env_modules : module_body MPmap.t;
  env_modtypes : module_type_body MPmap.t}

type stratification = {
  env_universes : universes;
  env_engagement : engagement option
}

type env = {
    env_globals       : globals;
    env_named_context : named_context;
    env_rel_context   : rel_context;
    env_stratification : stratification;
    env_imports : Digest.t MPmap.t }

let empty_env = {
  env_globals =
  { env_constants = Cmap_env.empty;
    env_inductives = Mindmap_env.empty;
    env_inductives_eq = KNmap.empty;
    env_modules = MPmap.empty;
    env_modtypes = MPmap.empty};
  env_named_context = [];
  env_rel_context = [];
  env_stratification =
  { env_universes = Univ.initial_universes;
    env_engagement = None};
  env_imports = MPmap.empty }

let engagement env = env.env_stratification.env_engagement
let universes env = env.env_stratification.env_universes
let named_context env = env.env_named_context
let rel_context env = env.env_rel_context

let set_engagement c env =
  match env.env_stratification.env_engagement with
    | Some c' -> if c=c' then env else error "Incompatible engagement"
    | None ->
        { env with env_stratification =
          { env.env_stratification with env_engagement = Some c } }

(* Digests *)

let add_digest env dp digest =
  { env with env_imports = MPmap.add (MPfile dp) digest env.env_imports }

let lookup_digest env dp =
  MPmap.find (MPfile dp) env.env_imports

(* Rel context *)
let lookup_rel n env =
  let rec lookup_rel n sign =
    match n, sign with
      | 1, decl :: _ -> decl
      | n, _ :: sign -> lookup_rel (n-1) sign
      | _, []        -> raise Not_found in
  lookup_rel n env.env_rel_context

let push_rel d env =
    { env with
      env_rel_context = d :: env.env_rel_context }

let push_rel_context ctxt x = fold_rel_context push_rel ctxt ~init:x

let push_rec_types (lna,typarray,_) env =
  let ctxt = array_map2_i (fun i na t -> (na, None, lift i t)) lna typarray in
  Array.fold_left (fun e assum -> push_rel assum e) env ctxt

(* Named context *)

let push_named d env =
(*  if not (env.env_rel_context = []) then raise (ASSERT env.env_rel_context);
  assert (env.env_rel_context = []); *)
    { env with
      env_named_context = d :: env.env_named_context }

let lookup_named id env =
  let rec lookup_named id = function
    | (id',_,_ as decl) :: _ when id=id' -> decl
    | _ :: sign -> lookup_named id sign
    | [] -> raise Not_found in
  lookup_named id env.env_named_context

(* A local const is evaluable if it is defined  *)

let named_type id env =
  let (_,_,t) = lookup_named id env in t

(* Universe constraints *)
let add_constraints c env =
  if c == Constraint.empty then
    env
  else
    let s = env.env_stratification in
    { env with env_stratification =
      { s with env_universes = merge_constraints c s.env_universes } }

(* Global constants *)

let lookup_constant kn env =
  Cmap_env.find kn env.env_globals.env_constants

let add_constant kn cs env =
  let new_constants =
    Cmap_env.add kn cs env.env_globals.env_constants in
  let new_globals =
    { env.env_globals with
	env_constants = new_constants } in
  { env with env_globals = new_globals }

type const_evaluation_result = NoBody | Opaque

exception NotEvaluableConst of const_evaluation_result

let constant_value env kn =
  let cb = lookup_constant kn env in
  if cb.const_opaque then raise (NotEvaluableConst Opaque);
  match cb.const_body with
    | Some l_body -> force_constr l_body
    | None -> raise (NotEvaluableConst NoBody)

(* A global const is evaluable if it is defined and not opaque *)
let evaluable_constant cst env =
  try let _  = constant_value env cst in true
  with Not_found | NotEvaluableConst _ -> false

(* Mutual Inductives *)
let scrape_mind env kn=
  try
    KNmap.find kn env.env_globals.env_inductives_eq
  with 
      Not_found -> kn

let mind_equiv env (kn1,i1) (kn2,i2) =
  i1 = i2 && 
  scrape_mind env (user_mind kn1) = scrape_mind env (user_mind kn2)


let lookup_mind kn env =
  Mindmap_env.find kn env.env_globals.env_inductives

let add_mind kn mib env =
  let new_inds = Mindmap_env.add kn mib env.env_globals.env_inductives in
  let kn1,kn2 =  user_mind kn,canonical_mind kn in
  let new_inds_eq = if kn1=kn2 then 
    env.env_globals.env_inductives_eq
  else
    KNmap.add kn1 kn2  env.env_globals.env_inductives_eq in
  let new_globals =
    { env.env_globals with
	env_inductives = new_inds;
	env_inductives_eq = new_inds_eq} in
  { env with env_globals = new_globals }


(* Modules *)

let add_modtype ln mtb env =
  let new_modtypes = MPmap.add ln mtb env.env_globals.env_modtypes in
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
  MPmap.find ln env.env_globals.env_modtypes
