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
open Univ
open Term
open Reduction
open Sign
open Declarations
open Inductive
open Environ
open Entries
open Typeops
open Type_errors
open Indtypes
open Term_typing
open Modops
open Subtyping
open Mod_typing

type modvariant = 
  | NONE 
  | SIG of (* funsig params *) (mod_bound_id * module_type_body) list 
  | STRUCT of (* functor params *) (mod_bound_id * module_type_body) list
      * (* optional result type *) module_type_body option
  | LIBRARY

type module_info = 
    { msid : mod_self_id;
      modpath : module_path;
      label : label;
      variant : modvariant}

let check_label l labset = 
  if Labset.mem l labset then error_existing_label l

type library_info = dir_path * Digest.t

type safe_environment = 
    { old : safe_environment;
      env : env;
      modinfo : module_info;
      labset : Labset.t;
      revsign : module_signature_body;
      imports : library_info list;
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
      msid = initial_msid;
      modpath = initial_path;
      label = mk_label "_";
      variant = NONE};
    labset = Labset.empty;
    revsign = [];
    imports = [];
    loads = [] }

let env_of_safe_env senv = senv.env
let env_of_senv = env_of_safe_env


(* Insertion of section variables. They are now typed before being
   added to the environment. *)

(* Same as push_named, but check that the variable is not already
   there. Should *not* be done in Environ because tactics add temporary
   hypothesis many many times, and the check performed here would
   cost too much. *)
let safe_push_named (id,_,_ as d) env =
  let _ =
    try
      let _ = lookup_named id env in 
      error ("identifier "^string_of_id id^" already defined")
    with Not_found -> () in
  Environ.push_named d env

let push_named_def (id,b,topt) senv =
  let (c,typ,cst) = translate_local_def senv.env (b,topt) in
  let env' = add_constraints cst senv.env in
  let env'' = safe_push_named (id,Some c,typ) env' in
  (cst, {senv with env=env''})

let push_named_assum (id,t) senv =
  let (t,cst) = translate_local_assum senv.env t in
  let env' = add_constraints cst senv.env in
  let env'' = safe_push_named (id,None,t) env' in
  (cst, {senv with env=env''})


(* Insertion of constants and parameters in environment. *)

type global_declaration = 
  | ConstantEntry of constant_entry
  | GlobalRecipe of Cooking.recipe

let add_constant dir l decl senv =
  check_label l senv.labset;
  let cb = match decl with 
      ConstantEntry ce -> translate_constant senv.env ce
    | GlobalRecipe r -> translate_recipe senv.env r
  in
  let env' = Environ.add_constraints cb.const_constraints senv.env in
  let kn = make_kn senv.modinfo.modpath dir l in
  let env'' = Environ.add_constant kn cb env' in
  kn, { old = senv.old;
	env = env'';
	modinfo = senv.modinfo;
	labset = Labset.add l senv.labset;
	revsign = (l,SPBconst cb)::senv.revsign;
	imports = senv.imports;
	loads = senv.loads }
    

(* Insertion of inductive types. *)

let add_mind dir l mie senv =
  if mie.mind_entry_inds = [] then 
    anomaly "empty inductive types declaration"; 
            (* this test is repeated by translate_mind *)
  let id = (List.nth mie.mind_entry_inds 0).mind_entry_typename in
  if l <> label_of_id id then
    anomaly ("the label of inductive packet and its first inductive"^
	     " type do not match");
  check_label l senv.labset; 
    (* TODO: when we will allow reorderings we will have to verify 
       all labels *)
  let mib = translate_mind senv.env mie in
  let env' = Environ.add_constraints mib.mind_constraints senv.env in
  let kn = make_kn senv.modinfo.modpath dir l in
  let env'' = Environ.add_mind kn mib env' in
  kn, { old = senv.old;
	env = env'';
	modinfo = senv.modinfo;
	labset = Labset.add l senv.labset;  (* TODO: the same as above *)
	revsign = (l,SPBmind mib)::senv.revsign;
	imports = senv.imports;
	loads = senv.loads }


(* Insertion of module types *)

let add_modtype l mte senv = 
  check_label l senv.labset; 
  let mtb = translate_modtype senv.env mte in
  let env' = add_modtype_constraints senv.env mtb in
  let kn = make_kn senv.modinfo.modpath empty_dirpath l in
  let env'' = Environ.add_modtype kn mtb env' in
  kn, { old = senv.old;
	env = env'';
	modinfo = senv.modinfo;
	labset = Labset.add l senv.labset;
	revsign = (l,SPBmodtype mtb)::senv.revsign;
	imports = senv.imports;
	loads = senv.loads }


(* Insertion of modules *)

let add_module l me senv = 
  check_label l senv.labset; 
  let mb = translate_module senv.env me in
  let env' = add_module_constraints senv.env mb in
  let mp = MPdot(senv.modinfo.modpath, l) in
  let env'' = Modops.add_module mp mb env' in
  mp, { old = senv.old;
	env = env'';
	modinfo = senv.modinfo;
	labset = Labset.add l senv.labset;
	revsign = (l,SPBmodule mb)::senv.revsign;
	imports = senv.imports;
	loads = senv.loads }


(* Interactive modules *)

let start_module dir l params result senv = 
  check_label l senv.labset; 
  let rec trans_params env = function 
    | [] -> env,[] 
    | (mbid,mte)::rest -> 
	let mtb = translate_modtype env mte in
	let env = 
	  Modops.add_module (MPbound mbid) (module_body mtb) env 
	in
	let env,transrest = trans_params env rest in
	env, (mbid,mtb)::transrest
  in
  let env,params_body = trans_params senv.env params in
  let check_sig mtb = match scrape_modtype env mtb with
    | MTBsig _ -> ()
    | MTBfunsig _ -> error_result_must_be_signature mtb 
    | _ -> anomaly "start_module: modtype not scraped"
  in
  let result_body = option_app (translate_modtype env) result in
  ignore (option_app check_sig result_body);
  let msid = make_msid dir (string_of_label l) in
  let mp = MPself msid in
  let modinfo = { msid = msid;
		  modpath = mp;
		  label = l;
		  variant = STRUCT(params_body,result_body) }
  in
  mp, { old = senv;
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
      | NONE | LIBRARY | SIG _ -> error_no_module_to_end ()
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
  mp, { old = oldsenv.old;
	env = newenv;
	modinfo = oldsenv.modinfo;
	labset = Labset.add l oldsenv.labset;
	revsign = (l,SPBmodule mb)::oldsenv.revsign;
	imports = senv.imports;
	loads = senv.loads@oldsenv.loads }


(* Interactive module types *)

let start_modtype dir l params senv = 
  check_label l senv.labset; 
  let rec trans_params env = function 
    | [] -> env,[] 
    | (mbid,mte)::rest -> 
	let mtb = translate_modtype env mte in
	let env = 
	  Modops.add_module (MPbound mbid) (module_body mtb) env 
	in
	let env,transrest = trans_params env rest in
	env, (mbid,mtb)::transrest
  in
  let env,params_body = trans_params senv.env params in
  let msid = make_msid dir (string_of_label l) in
  let mp = MPself msid in
  let modinfo = { msid = msid;
		  modpath = mp;
		  label = l;
		  variant = SIG params_body }
  in
  mp, { old = senv;
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
      | LIBRARY | NONE | STRUCT _ -> error_no_modtype_to_end ()
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
  let kn = make_kn oldsenv.modinfo.modpath empty_dirpath l in
  let newenv = oldsenv.env in
  let newenv = 
    List.fold_left
      (fun env (mp,mb) -> Modops.add_module mp mb env) 
      newenv
      senv.loads
  in
  let newenv = 
    Environ.add_modtype kn mtb newenv
  in 
  kn, { old = oldsenv.old;
	env = newenv;
	modinfo = oldsenv.modinfo;
	labset = Labset.add l oldsenv.labset;
	revsign = (l,SPBmodtype mtb)::oldsenv.revsign;
	imports = senv.imports;
	loads = senv.loads@oldsenv.loads }
  

let current_modpath senv = senv.modinfo.modpath
let current_msid senv = senv.modinfo.msid


let add_constraints cst senv = 
  {senv with env = Environ.add_constraints cst senv.env}



(* Libraries = Compiled modules *)

type compiled_library = 
    dir_path * module_type_body * library_info list


(* We check that only initial state Require's were performed before 
   [start_library] was called *)

let start_library dir senv =
  if not (senv.revsign = [] &&
	  senv.modinfo.msid = initial_msid &&
	  senv.modinfo.variant = NONE)
  then
    anomaly "Safe_typing.start_library: environment should be empty";
  let dir_path,l = 
    match (repr_dirpath dir) with
	[] -> anomaly "Empty dirpath in Safe_typing.start_library"
      | hd::tl ->
	  make_dirpath tl, label_of_id hd
  in
  let msid = make_msid dir_path (string_of_label l) in
  let mp = MPself msid in
  let modinfo = { msid = msid;
		  modpath = mp;
		  label = l;
		  variant = LIBRARY }
  in
  mp, { old = senv;
	env = senv.env;
	modinfo = modinfo;
	labset = Labset.empty;
	revsign = [];
	imports = senv.imports;
	loads = [] }


let export senv dp = 
  let modinfo = senv.modinfo in
  if modinfo.variant <> LIBRARY then
    anomaly "We are not exporting a library";
  (*if senv.modinfo.params <> [] || senv.modinfo.restype <> None then
    (* error_export_simple *) (); *)
  let mtb = MTBsig (modinfo.msid, List.rev senv.revsign) in
    modinfo.msid, (dp,mtb,senv.imports)


let import_constraints g kn cst =
  try
    merge_constraints cst g
  with UniverseInconsistency ->
    error "import_constraints: Universe Inconsistency during import"


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
  let mp = MPfile dp in
  let mb = module_body mtb in
  let env = senv.env in
(* <HACK> temporary -- only for libraries without module components *)
  let add_constraints env = function
    | _,SPBconst {const_constraints=constraints}  
    | _,SPBmind {mind_constraints=constraints} ->
	Environ.add_constraints constraints env
    | _ -> todo "We are not ready for module components yet!"; env
  in
  let env = match mtb with
    | MTBsig (_,sign) -> List.fold_left add_constraints env sign
    | _ -> todo "We are not ready for non-structure libraries"; env
  in
(* </HACK> *)
  mp, { senv with 
	  env = Modops.add_module mp mb env; 
	  imports = (dp,digest)::senv.imports;
	  loads = (mp,mb)::senv.loads }



type judgment = unsafe_judgment

let j_val j = j.uj_val
let j_type j = j.uj_type

let safe_infer senv = infer (env_of_senv senv)
    
let typing senv = Typeops.typing (env_of_senv senv)

