open CErrors
open Util
open Names
open Cic
open Term
open Declarations

type globals = {
  env_constants : constant_body Cmap_env.t;
  env_inductives : mutual_inductive_body Mindmap_env.t;
  env_inductives_eq : KerName.t KNmap.t;
  env_modules : module_body MPmap.t;
  env_modtypes : module_type_body MPmap.t}

type stratification = {
  env_universes : Univ.universes;
  env_engagement : engagement
}

type env = {
    env_globals       : globals;
    env_rel_context   : rel_context;
    env_stratification : stratification;
    env_imports : Cic.vodigest MPmap.t;
    env_conv_oracle : oracle; }

let empty_oracle = {
  var_opacity = Id.Map.empty;
  cst_opacity = Cmap.empty;
  var_trstate = Id.Pred.empty;
  cst_trstate = Cpred.empty;
}

let empty_env = {
  env_globals =
  { env_constants = Cmap_env.empty;
    env_inductives = Mindmap_env.empty;
    env_inductives_eq = KNmap.empty;
    env_modules = MPmap.empty;
    env_modtypes = MPmap.empty};
  env_rel_context = [];
  env_stratification =
  { env_universes = Univ.initial_universes;
    env_engagement = PredicativeSet };
  env_imports = MPmap.empty;
  env_conv_oracle = empty_oracle }

let engagement env = env.env_stratification.env_engagement
let universes env = env.env_stratification.env_universes
let rel_context env = env.env_rel_context

let set_engagement (impr_set as c) env =
  let expected_impr_set =
    env.env_stratification.env_engagement in
  begin
    match impr_set,expected_impr_set with
    | PredicativeSet, ImpredicativeSet -> user_err Pp.(str "Incompatible engagement")
    | _ -> ()
  end;
  { env with env_stratification =
      { env.env_stratification with env_engagement = c } }

let set_oracle env oracle = { env with env_conv_oracle = oracle }

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
  let ctxt = Array.map2_i (fun i na t -> LocalAssum (na, lift i t)) lna typarray in
  Array.fold_left (fun e assum -> push_rel assum e) env ctxt

(* Universe constraints *)
let map_universes f env =
  let s = env.env_stratification in
    { env with env_stratification =
	 { s with env_universes = f s.env_universes } }

let add_constraints c env =
  if c == Univ.Constraint.empty then env
  else map_universes (Univ.merge_constraints c) env
			   
let push_context ?(strict=false) ctx env =
  map_universes (Univ.merge_context strict ctx) env

let push_context_set ?(strict=false) ctx env =
  map_universes (Univ.merge_context_set strict ctx) env

let check_constraints cst env =
  Univ.check_constraints cst env.env_stratification.env_universes

(* Global constants *)

let lookup_constant kn env =
  Cmap_env.find kn env.env_globals.env_constants

let anomaly s = anomaly (Pp.str s)

let add_constant kn cs env =
  if Cmap_env.mem kn env.env_globals.env_constants then
    Printf.ksprintf anomaly ("Constant %s is already defined.")
      (Constant.to_string kn);
  let new_constants =
    Cmap_env.add kn cs env.env_globals.env_constants in
  let new_globals =
    { env.env_globals with
	env_constants = new_constants } in
  { env with env_globals = new_globals }

type const_evaluation_result = NoBody | Opaque

(* Constant types *)

let constraints_of cb u =
  match cb.const_universes with
  | Monomorphic_const _ -> Univ.Constraint.empty
  | Polymorphic_const ctx -> Univ.AUContext.instantiate u ctx

(* constant_type gives the type of a constant *)
let constant_type env (kn,u) =
  let cb = lookup_constant kn env in
  match cb.const_universes with
  | Monomorphic_const _ -> cb.const_type, Univ.Constraint.empty
  | Polymorphic_const ctx -> 
    let csts = constraints_of cb u in
    (subst_instance_constr u cb.const_type, csts)

exception NotEvaluableConst of const_evaluation_result

let constant_value env (kn,u) =
  let cb = lookup_constant kn env in
  match cb.const_body with
  | Def l_body ->
    let b = force_constr l_body in
    begin
      match cb.const_universes with
      | Monomorphic_const _ -> b
      | Polymorphic_const _ -> subst_instance_constr u (force_constr l_body)
    end
  | OpaqueDef _ -> raise (NotEvaluableConst Opaque)
  | Undef _ -> raise (NotEvaluableConst NoBody)

(* A global const is evaluable if it is defined and not opaque *)
let evaluable_constant cst env =
  try let _  = constant_value env (cst, Univ.Instance.empty) in true
  with Not_found | NotEvaluableConst _ -> false

(* Mutual Inductives *)
let scrape_mind env kn=
  try
    KNmap.find kn env.env_globals.env_inductives_eq
  with
    Not_found -> kn

let mind_equiv env (kn1,i1) (kn2,i2) =
  Int.equal i1 i2 &&
  KerName.equal
    (scrape_mind env (MutInd.user kn1))
    (scrape_mind env (MutInd.user kn2))


let lookup_mind kn env =
  Mindmap_env.find kn env.env_globals.env_inductives

let add_mind kn mib env =
  if Mindmap_env.mem kn env.env_globals.env_inductives then
    Printf.ksprintf anomaly ("Mutual inductive block %s is already defined.")
      (MutInd.to_string kn);
  let new_inds = Mindmap_env.add kn mib env.env_globals.env_inductives in
  let kn1,kn2 =  MutInd.user kn, MutInd.canonical kn in
  let new_inds_eq = if KerName.equal kn1 kn2 then
    env.env_globals.env_inductives_eq
  else
    KNmap.add kn1 kn2  env.env_globals.env_inductives_eq in
  let new_globals =
    { env.env_globals with
      env_inductives = new_inds;
      env_inductives_eq = new_inds_eq} in
  { env with env_globals = new_globals }

let lookup_projection p env =
  let mind,i = Projection.inductive p in
  let mib = lookup_mind mind env in
  match mib.mind_record with
  | NotRecord | FakeRecord -> CErrors.anomaly ~label:"lookup_projection" Pp.(str "not a projection")
  | PrimRecord infos ->
    let _,labs,typs = infos.(i) in
    let parg = Projection.arg p in
    if not (Label.equal labs.(parg) (Projection.label p))
    then CErrors.anomaly ~label:"lookup_projection" Pp.(str "incorrect label on projection")
    else if not (Int.equal mib.mind_nparams (Projection.npars p))
    then CErrors.anomaly ~label:"lookup_projection" Pp.(str "incorrect param number on projection")
    else typs.(parg)

(* Modules *)

let add_modtype ln mtb env =
  if MPmap.mem ln env.env_globals.env_modtypes then
    Printf.ksprintf anomaly ("Module type %s is already defined.")
      (ModPath.to_string ln);
  let new_modtypes = MPmap.add ln mtb env.env_globals.env_modtypes in
  let new_globals =
    { env.env_globals with
	env_modtypes = new_modtypes } in
  { env with env_globals = new_globals }

let shallow_add_module mp mb env =
  if MPmap.mem mp env.env_globals.env_modules then
    Printf.ksprintf anomaly ("Module %s is already defined.")
      (ModPath.to_string mp);
  let new_mods = MPmap.add mp mb env.env_globals.env_modules in
  let new_globals =
    { env.env_globals with
	env_modules = new_mods } in
  { env with env_globals = new_globals }

let shallow_remove_module mp env =
  if not (MPmap.mem mp env.env_globals.env_modules) then
    Printf.ksprintf anomaly ("Module %s is unknown.")
      (ModPath.to_string mp);
  let new_mods = MPmap.remove mp env.env_globals.env_modules in
  let new_globals =
    { env.env_globals with
	env_modules = new_mods } in
  { env with env_globals = new_globals }

let lookup_module mp env =
  MPmap.find mp env.env_globals.env_modules

let lookup_modtype ln env =
  MPmap.find ln env.env_globals.env_modtypes
