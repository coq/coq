(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util
open Identifier
open Names
open Declarations
open Mod_declarations
open Inductive
open Environ
open Type_errors
open Typeops
open Indtypes
open Term_typing
open Modops
open Subtyping
open Mod_typing
(*s Safe environments. *)

type modvariant = 
  | NONE 
  | SIG of (* funsig params *) (mod_bound_id * module_type_body) list 
  | STRUCT of (* functor params *) (mod_bound_id * module_type_body) list
      * (* optional result type *) module_type_body option

type module_info = 
    { msid : mod_str_id;
      modpath : module_path;
      label : label;
      variant : modvariant}

let check_label l labset = 
  if Labset.mem l labset then error_existing_label l

type compilation_unit_info = dir_path * Digest.t

type safe_environment = 
    { old : safe_environment;
      env : env;
      modinfo : module_info;
      labset : Labset.t;
      revsign : module_signature_body;
      imports : compilation_unit_info list;
      loads : (module_path * module_body) list }

(*
  { old = senv.old;
    env = ;
    modinfo = senv.modinfo;
    labset = ;
    revsign = ;
    imports = senv.imports ;
    loads = senv.loads }
*)


(* a small hack to avoid variants and an unused case in all functions *)
let rec empty_environment = 
  { old = empty_environment; 
    env = empty_env;
    modinfo = {
      msid = top_msid;
      modpath = top_path;
      label = label_of_string "_";
      variant = NONE};
    labset = Labset.empty;
    revsign = [];
    imports = [];
    loads = [] }

let env_of_senv senv = senv.env

let universes senv = universes (env_of_senv senv)

let lookup_named id senv = lookup_named id (env_of_senv senv)
let lookup_constant ln senv = lookup_constant ln (env_of_senv senv)
let lookup_mind ln senv = lookup_mind ln (env_of_senv senv)
let lookup_mind_specif ind senv = 
  lookup_mind_specif ind (env_of_senv senv)

let lookup_module mp senv = lookup_module mp (env_of_senv senv)
let lookup_modtype ln senv = lookup_modtype ln (env_of_senv senv)



(* Insertion of variables (named and de Bruijn'ed). They are now typed
   before being added to the environment. *)

let push_named_def (id,b) senv = 
  let (j,cst) = infer senv.env b in
  let env' = add_constraints cst senv.env in
    { senv with 
	env = Environ.push_named_def (id,j.uj_val,j.uj_type) env' }

let push_named_assum (id,t) senv = 
  let (j,cst) = infer senv.env t in
  let env' = add_constraints cst senv.env in
  let t = assumption_of_judgment senv.env Evd.empty j in
    { senv with
	env = Environ.push_named_assum (id,t) env' }

(* Insertion of constants and parameters in environment *)

let add_constant l ce senv = 
  check_label l senv.labset;
  let cb = translate_constant senv.env ce in
  let env' = Environ.add_constraints cb.const_constraints senv.env in
  let ln = make_ln senv.modinfo.modpath l in
  { old = senv.old;
    env = Environ.add_constant ln cb env';
    modinfo = senv.modinfo;
    labset = Labset.add l senv.labset;
    revsign = (l,SPBconst cb)::senv.revsign;
    imports = senv.imports;
    loads = senv.loads }, ln

(* Insertion of inductive types. *)

let add_mind mie senv =
  if mie.mind_entry_inds = [] then 
    anomaly "empty inductive types declaration"; 
            (* this test is repeated by translate_mind *)
  let l = (List.nth mie.mind_entry_inds 0).mind_entry_typename in
  check_label l senv.labset; 
    (* TODO: when we will allow reorderings we will have to verify 
       all labels *)
  let mib = translate_mind senv.env mie in
  let env' = Environ.add_constraints mib.mind_constraints senv.env in
  let ln = make_ln senv.modinfo.modpath l in
  { old = senv.old;
    env = Environ.add_mind ln mib env';
    modinfo = senv.modinfo;
    labset = Labset.add l senv.labset;  (* TODO: the same as above *)
    revsign = (l,SPBmind mib)::senv.revsign;
    imports = senv.imports;
    loads = senv.loads }, ln


let add_modtype l mte senv = 
  check_label l senv.labset; 
  let mtb = translate_modtype senv.env mte in
  let env' = add_modtype_constraints senv.env mtb in
  let ln = make_ln senv.modinfo.modpath l in
  { old = senv.old;
    env = Environ.add_modtype ln mtb env';
    modinfo = senv.modinfo;
    labset = Labset.add l senv.labset;
    revsign = (l,SPBmodtype mtb)::senv.revsign;
    imports = senv.imports;
    loads = senv.loads }, ln


let add_module l me senv =
  check_label l senv.labset; 
  let mb = translate_module senv.env me in
  let env' = add_module_constraints senv.env mb in
  let mp = MPdot(senv.modinfo.modpath, l) in
  { old = senv.old;
    env = Modops.add_module mp mb env';
    modinfo = senv.modinfo;
    labset = Labset.add l senv.labset;
    revsign = (l,SPBmodule mb)::senv.revsign;
    imports = senv.imports;
    loads = senv.loads }, mp


let begin_module l params result senv = 
  check_label l senv.labset; 
  let rec trans_params env = function 
    | [] -> env,[] 
    | (mbid,mte)::rest -> 
	let mtb = translate_modtype env mte in
	let env = 
	  Modops.add_module (MPbid mbid) (module_body mtb) env 
	in
	let env,transrest = trans_params env rest in
	env, (mbid,mtb)::transrest
  in
  let env,params_body = trans_params senv.env params in
  let check_sig mtb = match scrape_modtype env mtb with
    | MTBsig _ -> ()
    | MTBfunsig _ -> error_result_must_be_signature mtb 
    | _ -> anomaly "begin_module: modtype not scraped"
  in
  let result_body = option_app (translate_modtype env) result in
  ignore (option_app check_sig result_body);
  let msid = msid_of_string (string_of_label l) in
  let modinfo = { msid = msid;
		  modpath = MPsid msid;
		  label = l;
		  variant = STRUCT(params_body,result_body) }
  in
  { old = senv;
    env = env;
    modinfo = modinfo;
    labset = Labset.empty;
    revsign = [];
    imports = senv.imports;
    loads = [] }



let end_module l senv = 
  let oldsenv = senv.old in
  let modinfo = senv.modinfo in
  let params, restype = 
    match modinfo.variant with
      | NONE | SIG _ -> error_no_module_to_end ()
      | STRUCT(params,restype) -> (params,restype)
  in
  if l <> modinfo.label then error_incompatible_labels l modinfo.label;
  let auto_tb = MTBsig (modinfo.msid, List.rev senv.revsign) in
  let res_tb = 
    match restype with
      | None -> auto_tb
      | Some res_tb -> (check_subtypes senv.env auto_tb res_tb; res_tb)
  in
  let mtb = 
    List.fold_right 
      (fun (arg_id,arg_b) mtb -> MTBfunsig (arg_id,arg_b,mtb))
      params
      res_tb
  in
  let mb = module_body mtb in
  let mp = MPdot (oldsenv.modinfo.modpath, l) in
  let newenv = oldsenv.env in
  let newenv = 
    List.fold_left
      (fun env (mp,mb) -> Modops.add_module mp mb env) 
      newenv
      senv.loads
  in
  let newenv = 
    Modops.add_module mp mb newenv
  in 
  { old = oldsenv.old;
    env = newenv;
    modinfo = oldsenv.modinfo;
    labset = Labset.add l oldsenv.labset;
    revsign = (l,SPBmodule mb)::oldsenv.revsign;
    imports = senv.imports;
    loads = senv.loads@oldsenv.loads }, mp


let begin_modtype l params senv = 
  check_label l senv.labset; 
  let rec trans_params env = function 
    | [] -> env,[] 
    | (mbid,mte)::rest -> 
	let mtb = translate_modtype env mte in
	let env = 
	  Modops.add_module (MPbid mbid) (module_body mtb) env 
	in
	let env,transrest = trans_params env rest in
	env, (mbid,mtb)::transrest
  in
  let env,params_body = trans_params senv.env params in
  let msid = msid_of_string (string_of_label l) in
  let modinfo = { msid = msid;
		  modpath = MPsid msid;
		  label = l;
		  variant = SIG params_body }
  in
  { old = senv;
    env = env;
    modinfo = modinfo;
    labset = Labset.empty;
    revsign = [];
    imports = senv.imports;
    loads = [] }

let end_modtype l senv = 
  let oldsenv = senv.old in
  let modinfo = senv.modinfo in
  let params = 
    match modinfo.variant with
      | NONE | STRUCT _ -> error_no_modtype_to_end ()
      | SIG params -> params
  in
  if l <> modinfo.label then error_incompatible_labels l modinfo.label;
  let res_tb = MTBsig (modinfo.msid, List.rev senv.revsign) in
  let mtb = 
    List.fold_right 
      (fun (arg_id,arg_b) mtb -> MTBfunsig (arg_id,arg_b,mtb))
      params
      res_tb
  in
  let ln = make_ln oldsenv.modinfo.modpath l in
  let newenv = oldsenv.env in
  let newenv = 
    List.fold_left
      (fun env (mp,mb) -> Modops.add_module mp mb env) 
      newenv
      senv.loads
  in
  let newenv = 
    Environ.add_modtype ln mtb newenv
  in 
  { old = oldsenv.old;
    env = newenv;
    modinfo = oldsenv.modinfo;
    labset = Labset.add l oldsenv.labset;
    revsign = (l,SPBmodtype mtb)::oldsenv.revsign;
    imports = senv.imports;
    loads = senv.loads@oldsenv.loads }, ln
  

let current_modpath senv = senv.modinfo.modpath
let current_msid senv = senv.modinfo.msid

(* Other environment functionnality *)

let set_opaque senv = Environ.set_opaque (env_of_senv senv)
let set_transparent senv = Environ.set_transparent (env_of_senv senv)

type compiled_module = 
    dir_path * module_type_body * compilation_unit_info list

let export senv dp = 
  let modinfo = senv.modinfo in
  (*if senv.modinfo.params <> [] || senv.modinfo.restype <> None then
    (* error_export_simple *) (); *)
  let mtb = MTBsig (modinfo.msid, List.rev senv.revsign) in
    modinfo.msid, (dp,mtb,senv.imports)


let check_imports senv needed =
  let imports = senv.imports in
  let check (id,stamp) =
    try
      let actual_stamp = List.assoc id imports in
      if stamp <> actual_stamp then
	error ("Inconsistent assumptions over module " ^(string_of_dirpath id))
    with Not_found -> 
      error ("Reference to unknown module " ^ (string_of_dirpath id))
  in
  List.iter check needed


(* we have an inefficiency: Since loaded files are added to the
environment every time a module is closed, their components are
calculated many times. Thic could be avoided in several ways:

1 - for each file create a dummy environment containing only this
file's components, merge this environment with the global
environment, and store for the future (instead of just its type)
The function Modops.add_module could be used unchanged.

2 - create "persistent modules" environment table in Environ add put
loaded by side-effect once and for all (like it is done in OCaml).
Would this be correct with respect to undo's and stuff ?
*)
 
let import (dp,mtb,depends) digest senv = 
  check_imports senv depends;
  let mp = MPcomp dp in
  let mb = module_body mtb in
  { senv with 
      env = Modops.add_module mp mb senv.env; 
      imports = (dp,digest)::senv.imports;
      loads = (mp,mb)::senv.loads }, mp

let env_of_safe_env = env_of_senv

(* Exported typing functions *)

type judgment = unsafe_judgment

let j_val j = j.uj_val
let j_type j = j.uj_type

let safe_infer senv = infer (env_of_senv senv)
    
let typing_in_unsafe_env env c = 
  let (j,cst) = infer env c in
  j

let typing senv = typing_in_unsafe_env (env_of_senv senv)



