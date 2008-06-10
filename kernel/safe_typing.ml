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
open Mod_subst

type modvariant = 
  | NONE 
  | SIG of (* funsig params *) (mod_bound_id * module_type_body) list 
  | STRUCT of (* functor params *) (mod_bound_id * module_type_body) list
  | LIBRARY of dir_path

type module_info = 
    { msid : mod_self_id;
      modpath : module_path;
      seed : dir_path; (* the "seed" of unique identifier generator *)
      label : label;
      variant : modvariant;
      alias_subst : substitution}

let check_label l labset = 
  if Labset.mem l labset then error_existing_label l

let set_engagement_opt oeng env =
  match oeng with
      Some eng -> set_engagement eng env
    | _ -> env

type library_info = dir_path * Digest.t

type safe_environment = 
    { old : safe_environment;
      env : env;
      modinfo : module_info;
      labset : Labset.t;
      revstruct : structure_body;
      univ : Univ.constraints;
      engagement : engagement option;
      imports : library_info list;
      loads : (module_path * module_body) list;
      local_retroknowledge : Retroknowledge.action list}

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
      seed = initial_dir;
      label = mk_label "_";
      variant = NONE;
      alias_subst = empty_subst};
    labset = Labset.empty;
    revstruct = [];
    univ = Univ.Constraint.empty;
    engagement = None;
    imports = [];
    loads = [];
    local_retroknowledge = [] }

let env_of_safe_env senv = senv.env
let env_of_senv = env_of_safe_env










(*spiwack: functions for safe retroknowledge *)

(* terms which are closed under the environnement env, i.e
   terms which only depends on constant who are themselves closed *)
let closed env term = 
  ContextObjectMap.is_empty (assumptions env term)

(* the set of safe terms in an environement any recursive set of
   terms who are known not to prove inconsistent statement. It should
   include at least all the closed terms. But it could contain other ones
   like the axiom of excluded middle for instance *)
let safe =
  closed



(* universal lifting, used for the "get" operations mostly *)
let retroknowledge f senv = 
  Environ.retroknowledge f (env_of_senv senv)

let register senv field value by_clause = 
  (* todo : value closed, by_clause safe, by_clause of the proper type*)
  (* spiwack : updates the safe_env with the information that the register
     action has to be performed (again) when the environement is imported *)
  {senv with env = Environ.register senv.env field value;
             local_retroknowledge = 
      Retroknowledge.RKRegister (field,value)::senv.local_retroknowledge
  }

(* spiwack : currently unused *)
let unregister senv field  =
  (*spiwack: todo: do things properly or delete *)
  {senv with env = Environ.unregister senv.env field}
(* /spiwack *)










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

let hcons_constant_type = function
  | NonPolymorphicType t ->
      NonPolymorphicType (hcons1_constr t)
  | PolymorphicArity (ctx,s) ->
      PolymorphicArity (map_rel_context hcons1_constr ctx,s)

let hcons_constant_body cb =
  let body = match cb.const_body with
      None -> None
    | Some l_constr -> let constr = Declarations.force l_constr in
	Some (Declarations.from_val (hcons1_constr constr))
  in
    { cb with
	const_body = body;
	const_type = hcons_constant_type cb.const_type }

let add_constant dir l decl senv =
  check_label l senv.labset;
  let kn = make_con senv.modinfo.modpath dir l in
  let cb = 
    match decl with 
      | ConstantEntry ce -> translate_constant senv.env kn ce
      | GlobalRecipe r ->
	  let cb = translate_recipe senv.env kn r in
	    if dir = empty_dirpath then hcons_constant_body cb else cb
  in
  let env' = Environ.add_constraints cb.const_constraints senv.env in
  let env'' = Environ.add_constant kn cb env' in
    kn, { old = senv.old;
	  env = env'';
	  modinfo = senv.modinfo;
	  labset = Labset.add l senv.labset;
	  revstruct = (l,SFBconst cb)::senv.revstruct;
          univ = senv.univ;
          engagement = senv.engagement;
	  imports = senv.imports;
	  loads = senv.loads ;
	  local_retroknowledge = senv.local_retroknowledge }
    

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
	revstruct = (l,SFBmind mib)::senv.revstruct;
        univ = senv.univ;
        engagement = senv.engagement;
	imports = senv.imports;
	loads = senv.loads;
        local_retroknowledge = senv.local_retroknowledge }

(* Insertion of orphaned universe constraints *)

let add_constraints cst senv = 
  {senv with
    env = Environ.add_constraints cst senv.env;
    univ = Univ.Constraint.union cst senv.univ }

(* Insertion of module types *)

let add_modtype l mte senv = 
  check_label l senv.labset; 
  let mtb_expr,sub = translate_struct_entry senv.env mte  in
  let mtb = { typ_expr = mtb_expr;
	      typ_strength = None;
	      typ_alias = sub} in
  let env' = add_modtype_constraints senv.env mtb in
  let mp = MPdot(senv.modinfo.modpath, l) in
  let env'' = Environ.add_modtype mp mtb env' in
  mp, { old = senv.old;
	env = env'';
	modinfo = senv.modinfo;
	labset = Labset.add l senv.labset;
	revstruct = (l,SFBmodtype mtb)::senv.revstruct;
        univ = senv.univ;
        engagement = senv.engagement;
	imports = senv.imports;
	loads = senv.loads;
        local_retroknowledge = senv.local_retroknowledge }


(* full_add_module adds module with universes and constraints *)
let full_add_module mp mb env =
  let env = add_module_constraints env mb in
  let env = Modops.add_module mp mb env in
    env

(* Insertion of modules *)

let add_module l me senv = 
  check_label l senv.labset; 
  let mb = translate_module senv.env me in
  let mp = MPdot(senv.modinfo.modpath, l) in
  let env' = full_add_module mp mb senv.env in
  let is_functor,sub = Modops.update_subst senv.env mb mp in
  mp, { old = senv.old;
	env = env';
	modinfo = 
      if is_functor then
	senv.modinfo
      else
	{senv.modinfo with 
	   alias_subst = join senv.modinfo.alias_subst sub};
	labset = Labset.add l senv.labset;
	revstruct = (l,SFBmodule mb)::senv.revstruct;
        univ = senv.univ;
        engagement = senv.engagement;
	imports = senv.imports;
	loads = senv.loads;
        local_retroknowledge = senv.local_retroknowledge }

let add_alias l mp senv =
  check_label l senv.labset; 
  let mp' = MPdot(senv.modinfo.modpath, l) in
  (* we get all updated alias substitutions that comes from mp *)
  let _,sub = Modops.update_subst senv.env (lookup_module mp senv.env) mp in
   (* we add the new one *)
  let mp1 = scrape_alias mp senv.env in
  let sub = update_subst sub (map_mp mp' mp) in
  let sub = join (map_mp mp' mp1) sub in
  let env' = register_alias mp' mp senv.env in
    mp', { old = senv.old;
	env = env';
	modinfo = { senv.modinfo with 
		      alias_subst = join 
	    senv.modinfo.alias_subst sub};
	labset = Labset.add l senv.labset;
	revstruct = (l,SFBalias (mp,None))::senv.revstruct;
        univ = senv.univ;
        engagement = senv.engagement;
	imports = senv.imports;
	loads = senv.loads;
        local_retroknowledge = senv.local_retroknowledge }

(* Interactive modules *)

let start_module l senv = 
  check_label l senv.labset; 
  let msid = make_msid senv.modinfo.seed (string_of_label l) in
  let mp = MPself msid in
  let modinfo = { msid = msid;
		  modpath = mp;
		  seed = senv.modinfo.seed;
		  label = l;
		  variant = STRUCT [];
		  alias_subst = empty_subst}
  in
  mp, { old = senv;
	env = senv.env;
	modinfo = modinfo;
	labset = Labset.empty;
	revstruct = [];
        univ = Univ.Constraint.empty;
        engagement = None;
	imports = senv.imports;
	loads = [];
	(* spiwack : not sure, but I hope it's correct *)
        local_retroknowledge = [] }

let end_module l restype senv = 
  let oldsenv = senv.old in
  let modinfo = senv.modinfo in
  let restype = Option.map (translate_struct_entry senv.env) restype in
  let params,is_functor = 
    match modinfo.variant with
      | NONE | LIBRARY _ | SIG _ -> error_no_module_to_end ()
      | STRUCT params -> params, (List.length params > 0)
  in
  if l <> modinfo.label then error_incompatible_labels l modinfo.label;
  if not (empty_context senv.env) then error_local_context None;
  let functorize_struct tb = 
    List.fold_left
      (fun mtb (arg_id,arg_b) -> 
	SEBfunctor(arg_id,arg_b,mtb))
      tb
      params
  in
   let auto_tb = 
     SEBstruct (modinfo.msid, List.rev senv.revstruct)
  in
  let mod_typ,subst,cst = 
    match restype with
      | None ->  None,modinfo.alias_subst,Constraint.empty
      | Some (res_tb,subst) -> 
	  let cst = check_subtypes senv.env
	    {typ_expr = auto_tb;
	     typ_strength = None;
	     typ_alias = modinfo.alias_subst}
	    {typ_expr = res_tb;
	     typ_strength = None;
	     typ_alias = subst} in
	  let mtb = functorize_struct res_tb in
	    Some mtb,subst,cst
  in
  let mexpr = functorize_struct auto_tb in
  let cst = Constraint.union cst senv.univ in
  let mb = 
    { mod_expr = Some mexpr;
      mod_type = mod_typ;
      mod_constraints = cst;
      mod_alias = subst;
      mod_retroknowledge = senv.local_retroknowledge }
  in
  let mp = MPdot (oldsenv.modinfo.modpath, l) in
  let newenv = oldsenv.env in
  let newenv = set_engagement_opt senv.engagement newenv in
  let newenv = 
    List.fold_left
      (fun env (mp,mb) -> full_add_module mp mb env) 
      newenv
      (List.rev senv.loads)
  in
  let newenv = 
    full_add_module mp mb newenv
  in 
  let is_functor,subst = Modops.update_subst newenv mb mp in
  let newmodinfo = 
    if is_functor then
      oldsenv.modinfo
    else
      { oldsenv.modinfo with 
	  alias_subst = join 
	  oldsenv.modinfo.alias_subst 
	  subst };
  in
    mp, { old = oldsenv.old;
	env = newenv;
	modinfo = newmodinfo;
	labset = Labset.add l oldsenv.labset;
	revstruct = (l,SFBmodule mb)::oldsenv.revstruct;
        univ = oldsenv.univ;
        (* engagement is propagated to the upper level *)
        engagement = senv.engagement;
	imports = senv.imports;
	loads = senv.loads@oldsenv.loads;
	local_retroknowledge = senv.local_retroknowledge@oldsenv.local_retroknowledge }


(* Include for module and module type*)
 let add_include me senv =
   let struct_expr,_ =  translate_struct_entry senv.env me in
   let senv = add_constraints (struct_expr_constraints struct_expr) senv in
   let msid,str = match (eval_struct senv.env struct_expr) with
     | SEBstruct(msid,str_l) -> msid,str_l
     | _ -> error ("You cannot Include a higher-order Module or Module Type" )
   in
   let mp_sup = senv.modinfo.modpath in
   let str1 = subst_signature_msid msid mp_sup str in
   let add senv (l,elem)  = 
     check_label l senv.labset;
     match elem with
       | SFBconst cb ->
	   let con = make_con mp_sup empty_dirpath l in
	   let env' = Environ.add_constraints cb.const_constraints senv.env in
	   let env'' = Environ.add_constant con cb env' in
	     { old = senv.old;
	       env = env'';
	       modinfo = senv.modinfo;
	       labset = Labset.add l senv.labset;
	       revstruct = (l,SFBconst cb)::senv.revstruct;
               univ = senv.univ;
               engagement = senv.engagement;
	       imports = senv.imports;
	       loads = senv.loads ;
	       local_retroknowledge = senv.local_retroknowledge }
	       	     
       | SFBmind mib ->
	   let kn = make_kn mp_sup empty_dirpath l in
	   let env' = Environ.add_constraints mib.mind_constraints senv.env in
	   let env'' = Environ.add_mind kn mib env' in
	     { old = senv.old;
	       env = env'';
	       modinfo = senv.modinfo;
	       labset = Labset.add l senv.labset;  
	       revstruct = (l,SFBmind mib)::senv.revstruct;
               univ = senv.univ;
               engagement = senv.engagement;
	       imports = senv.imports;
	       loads = senv.loads;
               local_retroknowledge = senv.local_retroknowledge }
	       
       | SFBmodule mb ->
	   let mp = MPdot(senv.modinfo.modpath, l) in
	   let is_functor,sub = Modops.update_subst senv.env mb mp in
	   let env' = full_add_module mp mb senv.env in
	     { old = senv.old;
	       env = env';
	       modinfo = 
		 if is_functor then
		   senv.modinfo
		 else
		   {senv.modinfo with 
		      alias_subst = join senv.modinfo.alias_subst sub};
	       labset = Labset.add l senv.labset;
	       revstruct = (l,SFBmodule mb)::senv.revstruct;
	       univ = senv.univ;
	       engagement = senv.engagement;
	       imports = senv.imports;
	       loads = senv.loads;
	       local_retroknowledge = senv.local_retroknowledge }
       | SFBalias (mp',cst) ->
	   let env' = Option.fold_right 
	     Environ.add_constraints cst senv.env in
	   let mp = MPdot(senv.modinfo.modpath, l) in
	   let env' = register_alias mp mp' env' in
	     { old = senv.old;
	       env = env';
	       modinfo = senv.modinfo;
	       labset = Labset.add l senv.labset;
	       revstruct = (l,SFBalias (mp',cst))::senv.revstruct;
               univ = senv.univ;
               engagement = senv.engagement;
	       imports = senv.imports;
	       loads = senv.loads;
               local_retroknowledge = senv.local_retroknowledge }
       | SFBmodtype mtb ->
	   let env' = add_modtype_constraints senv.env mtb in
	   let mp = MPdot(senv.modinfo.modpath, l) in
	   let env'' = Environ.add_modtype mp mtb env' in
	     { old = senv.old;
	       env = env'';
	       modinfo = senv.modinfo;
	       labset = Labset.add l senv.labset;
	       revstruct = (l,SFBmodtype mtb)::senv.revstruct;
               univ = senv.univ;
               engagement = senv.engagement;
	       imports = senv.imports;
	       loads = senv.loads;
               local_retroknowledge = senv.local_retroknowledge }
   in
     List.fold_left add senv str1
	   
(* Adding parameters to modules or module types *)

let add_module_parameter mbid mte senv =
  if  senv.revstruct <> [] or senv.loads <> [] then
    anomaly "Cannot add a module parameter to a non empty module";
  let mtb_expr,sub = translate_struct_entry senv.env mte in
  let mtb = {typ_expr = mtb_expr;
	    typ_strength = None;
	    typ_alias = sub} in
  let env = full_add_module (MPbound mbid) (module_body_of_type mtb) senv.env 
  in
  let new_variant = match senv.modinfo.variant with
    | STRUCT params -> STRUCT ((mbid,mtb) :: params)
    | SIG params -> SIG ((mbid,mtb) :: params)
    | _ -> 
	anomaly "Module parameters can only be added to modules or signatures"
  in
  { old = senv.old;
    env = env;
    modinfo = { senv.modinfo with variant = new_variant };
    labset = senv.labset;
    revstruct = [];
    univ = senv.univ;
    engagement = senv.engagement;
    imports = senv.imports;
    loads = [];
    local_retroknowledge = senv.local_retroknowledge }


(* Interactive module types *)

let start_modtype l senv = 
  check_label l senv.labset; 
  let msid = make_msid senv.modinfo.seed (string_of_label l) in
  let mp = MPself msid in
  let modinfo = { msid = msid;
		  modpath = mp;
		  seed = senv.modinfo.seed;
		  label = l;
		  variant = SIG [];
		  alias_subst = empty_subst }
  in
  mp, { old = senv;
	env = senv.env;
	modinfo = modinfo;
	labset = Labset.empty;
	revstruct = [];
        univ = Univ.Constraint.empty;
        engagement = None;
	imports = senv.imports;
	loads = [] ;
	(* spiwack: not 100% sure, but I think it should be like that *)
        local_retroknowledge = []}

let end_modtype l senv = 
  let oldsenv = senv.old in
  let modinfo = senv.modinfo in
  let params = 
    match modinfo.variant with
      | LIBRARY _ | NONE | STRUCT _ -> error_no_modtype_to_end ()
      | SIG params -> params
  in
  if l <> modinfo.label then error_incompatible_labels l modinfo.label;
  if not (empty_context senv.env) then error_local_context None;
  let auto_tb = 
     SEBstruct (modinfo.msid, List.rev senv.revstruct)
  in
  let mtb_expr = 
    List.fold_left
      (fun mtb (arg_id,arg_b) -> 
	 SEBfunctor(arg_id,arg_b,mtb))
      auto_tb
      params
  in
  let mp = MPdot (oldsenv.modinfo.modpath, l) in
  let newenv = oldsenv.env in
  (* since universes constraints cannot be stored in the modtype,
     they are propagated to the upper level *)
  let newenv = Environ.add_constraints senv.univ  newenv in
  let newenv = set_engagement_opt senv.engagement newenv in
  let newenv = 
    List.fold_left
      (fun env (mp,mb) -> full_add_module mp mb env) 
      newenv
      (List.rev senv.loads)
  in
  let subst = senv.modinfo.alias_subst in
  let mtb = {typ_expr = mtb_expr;
	    typ_strength = None;
	    typ_alias = subst} in
  let newenv = 
    add_modtype_constraints newenv mtb
  in
  let newenv = 
    Environ.add_modtype mp mtb newenv
  in 
  mp, { old = oldsenv.old;
	env = newenv;
	modinfo = oldsenv.modinfo;
	labset = Labset.add l oldsenv.labset;
	revstruct = (l,SFBmodtype mtb)::oldsenv.revstruct;
        univ = Univ.Constraint.union senv.univ oldsenv.univ;
        engagement = senv.engagement;
	imports = senv.imports;
	loads = senv.loads@oldsenv.loads;
        (* spiwack : if there is a bug with retroknowledge in nested modules
                     it's likely to come from here *)
        local_retroknowledge = 
                   senv.local_retroknowledge@oldsenv.local_retroknowledge}
  

let current_modpath senv = senv.modinfo.modpath
let current_msid senv = senv.modinfo.msid


(* Check that the engagement expected by a library matches the initial one *)
let check_engagement env c =
  match Environ.engagement env, c with
    | Some ImpredicativeSet, Some ImpredicativeSet -> ()
    | _, None -> ()
    | _, Some ImpredicativeSet ->
        error "Needs option -impredicative-set"

let set_engagement c senv =
  {senv with
    env = Environ.set_engagement c senv.env;
    engagement = Some c }

(* Libraries = Compiled modules *)

type compiled_library = 
    dir_path * module_body * library_info list * engagement option

(* We check that only initial state Require's were performed before 
   [start_library] was called *)

let is_empty senv =
  senv.revstruct = [] &&
  senv.modinfo.msid = initial_msid &&
  senv.modinfo.variant = NONE

let start_library dir senv =
  if not (is_empty senv) then
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
		  seed = dir;
		  label = l;
		  variant = LIBRARY dir;
		  alias_subst = empty_subst }
  in
  mp, { old = senv;
	env = senv.env;
	modinfo = modinfo;
	labset = Labset.empty;
	revstruct = [];
        univ = Univ.Constraint.empty;
        engagement = None;
	imports = senv.imports;
	loads = [];
        local_retroknowledge = [] }



let export senv dir = 
  let modinfo = senv.modinfo in
  begin
    match modinfo.variant with
      | LIBRARY dp -> 
	  if dir <> dp then
	    anomaly "We are not exporting the right library!"
      | _ ->
	  anomaly "We are not exporting the library"
  end;
  (*if senv.modinfo.params <> [] || senv.modinfo.restype <> None then
    (* error_export_simple *) (); *)
  let mb = 
    { mod_expr = Some (SEBstruct (modinfo.msid, List.rev senv.revstruct));
      mod_type = None;
      mod_constraints = senv.univ;
      mod_alias = senv.modinfo.alias_subst;
      mod_retroknowledge = senv.local_retroknowledge}
  in
    modinfo.msid, (dir,mb,senv.imports,engagement senv.env)


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

2 - create "persistent modules" environment table in Environ add put
loaded by side-effect once and for all (like it is done in OCaml).
Would this be correct with respect to undo's and stuff ?
*)
 
let import (dp,mb,depends,engmt) digest senv = 
  check_imports senv depends;
  check_engagement senv.env engmt;
  let mp = MPfile dp in
  let env = senv.env in
  mp, { senv with 
	  env = full_add_module mp mb env; 
	  imports = (dp,digest)::senv.imports;
	  loads = (mp,mb)::senv.loads }


(* Remove the body of opaque constants in modules *)
 let rec lighten_module mb =
  { mb with
    mod_expr = Option.map lighten_modexpr mb.mod_expr;
    mod_type = Option.map lighten_modexpr mb.mod_type;
  }
    
and lighten_struct struc = 
  let lighten_body (l,body) = (l,match body with
    | SFBconst ({const_opaque=true} as x) -> SFBconst {x with const_body=None}
    | (SFBconst _ | SFBmind _ | SFBalias _) as x -> x
    | SFBmodule m -> SFBmodule (lighten_module m)
    | SFBmodtype m -> SFBmodtype 
	({m with 
	    typ_expr = lighten_modexpr m.typ_expr}))
  in
    List.map lighten_body struc

and lighten_modexpr = function
  | SEBfunctor (mbid,mty,mexpr) ->
      SEBfunctor (mbid, 
		    ({mty with 
			typ_expr = lighten_modexpr mty.typ_expr}),
		  lighten_modexpr mexpr)
  | SEBident mp as x -> x
  | SEBstruct (msid, struc) ->
      SEBstruct (msid, lighten_struct struc)
  | SEBapply (mexpr,marg,u) ->
      SEBapply (lighten_modexpr mexpr,lighten_modexpr marg,u)
  | SEBwith (seb,wdcl) ->
      SEBwith (lighten_modexpr seb,wdcl) 
 
let lighten_library (dp,mb,depends,s) = (dp,lighten_module mb,depends,s)


type judgment = unsafe_judgment

let j_val j = j.uj_val
let j_type j = j.uj_type

let safe_infer senv = infer (env_of_senv senv)
    
let typing senv = Typeops.typing (env_of_senv senv)



