(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Jean-Christophe Filliâtre as part of the rebuilding of
   Coq around a purely functional abstract type-checker, Dec 1999 *)

(* This file provides the entry points to the kernel type-checker. It
   defines the abstract type of well-formed environments and
   implements the rules that build well-formed environments.

   An environment is made of constants and inductive types (E), of
   section declarations (Delta), of local bound-by-index declarations
   (Gamma) and of universe constraints (C). Below E[Delta,Gamma] |-_C
   means that the tuple E, Delta, Gamma, C is a well-formed
   environment. Main rules are:

   empty_environment:

     ------
     [,] |-

   push_named_assum(a,T):
   
     E[Delta,Gamma] |-_G
     ------------------------
     E[Delta,Gamma,a:T] |-_G'

   push_named_def(a,t,T):
   
     E[Delta,Gamma] |-_G
     ---------------------------
     E[Delta,Gamma,a:=t:T] |-_G'

   add_constant(ConstantEntry(DefinitionEntry(c,t,T))):

     E[Delta,Gamma] |-_G
     ---------------------------
     E,c:=t:T[Delta,Gamma] |-_G'

   add_constant(ConstantEntry(ParameterEntry(c,T))):

     E[Delta,Gamma] |-_G
     ------------------------
     E,c:T[Delta,Gamma] |-_G'

   add_mind(Ind(Ind[Gamma_p](Gamma_I:=Gamma_C))):

     E[Delta,Gamma] |-_G
     ------------------------
     E,Ind[Gamma_p](Gamma_I:=Gamma_C)[Delta,Gamma] |-_G'

   etc.
*)

open Errors
open Util
open Names
open Univ
open Declarations
open Environ
open Entries
open Typeops
open Modops
open Subtyping
open Mod_typing
open Mod_subst


type modvariant =
  | NONE
  | SIG of (* funsig params *) (MBId.t * module_type_body) list
  | STRUCT of (* functor params *) (MBId.t * module_type_body) list
  | LIBRARY of DirPath.t

type module_info =
    {modpath : module_path;
     label : Label.t;
     variant : modvariant;
     resolver : delta_resolver;
     resolver_of_param : delta_resolver;}

let set_engagement_opt oeng env =
  match oeng with
      Some eng -> set_engagement eng env
    | _ -> env

type library_info = DirPath.t * Digest.t

type safe_environment =
    { old : safe_environment;
      env : env;
      modinfo : module_info;
      modlabels : Label.Set.t;
      objlabels : Label.Set.t;
      revstruct : structure_body;
      univ : Univ.constraints;
      engagement : engagement option;
      imports : library_info list;
      loads : (module_path * module_body) list;
      local_retroknowledge : Retroknowledge.action list}

let exists_modlabel l senv = Label.Set.mem l senv.modlabels
let exists_objlabel l senv = Label.Set.mem l senv.objlabels

let check_modlabel l senv =
  if exists_modlabel l senv then error_existing_label l
let check_objlabel l senv =
  if exists_objlabel l senv then error_existing_label l

let check_objlabels ls senv =
  Label.Set.iter (fun l -> check_objlabel l senv) ls

let labels_of_mib mib =
  let add,get =
    let labels = ref Label.Set.empty in
    (fun id -> labels := Label.Set.add (Label.of_id id) !labels),
    (fun () -> !labels)
  in
  let visit_mip mip =
    add mip.mind_typename;
    Array.iter add mip.mind_consnames
  in
  Array.iter visit_mip mib.mind_packets;
  get ()

(* a small hack to avoid variants and an unused case in all functions *)
let rec empty_environment =
  { old = empty_environment;
    env = empty_env;
    modinfo = {
      modpath = initial_path;
      label = Label.make "_";
      variant = NONE;
      resolver = empty_delta_resolver;
      resolver_of_param = empty_delta_resolver};
    modlabels = Label.Set.empty;
    objlabels = Label.Set.empty;
    revstruct = [];
    univ = Univ.empty_constraint;
    engagement = None;
    imports = [];
    loads = [];
    local_retroknowledge = [] }

let env_of_safe_env senv = senv.env
let env_of_senv = env_of_safe_env

let add_constraints cst senv =
  { senv with
    env = Environ.add_constraints cst senv.env;
    univ = Univ.union_constraints cst senv.univ }

let constraints_of_sfb = function
  | SFBconst cb -> cb.const_constraints
  | SFBmind mib -> mib.mind_constraints
  | SFBmodtype mtb -> mtb.typ_constraints
  | SFBmodule mb -> mb.mod_constraints

(* A generic function for adding a new field in a same environment.
   It also performs the corresponding [add_constraints]. *)

type generic_name =
  | C of constant
  | I of mutual_inductive
  | MT of module_path
  | M

let add_field ((l,sfb) as field) gn senv =
  let mlabs,olabs = match sfb with
    | SFBmind mib ->
      let l = labels_of_mib mib in
      check_objlabels l senv; (Label.Set.empty,l)
    | SFBconst _ ->
      check_objlabel l senv; (Label.Set.empty, Label.Set.singleton l)
    | SFBmodule _ | SFBmodtype _ ->
      check_modlabel l senv; (Label.Set.singleton l, Label.Set.empty)
  in
  let senv = add_constraints (constraints_of_sfb sfb) senv in
  let env' = match sfb, gn with
    | SFBconst cb, C con -> Environ.add_constant con cb senv.env
    | SFBmind mib, I mind -> Environ.add_mind mind mib senv.env
    | SFBmodtype mtb, MT mp -> Environ.add_modtype mp mtb senv.env
    | SFBmodule mb, M -> Modops.add_module mb senv.env
    | _ -> assert false
  in
  { senv with
    env = env';
    modlabels = Label.Set.union mlabs senv.modlabels;
    objlabels = Label.Set.union olabs senv.objlabels;
    revstruct = field :: senv.revstruct }

(* Applying a certain function to the resolver of a safe environment *)

let update_resolver f senv =
  let mi = senv.modinfo in
  { senv with modinfo = { mi with resolver = f mi.resolver }}


(* universal lifting, used for the "get" operations mostly *)
let retroknowledge f senv =
  Environ.retroknowledge f (env_of_senv senv)

let register senv field value by_clause =
  (* todo : value closed, by_clause safe, by_clause of the proper type*)
  (* spiwack : updates the safe_env with the information that the register
     action has to be performed (again) when the environement is imported *)
  {senv with
    env = Environ.register senv.env field value;
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
      error ("Identifier "^Id.to_string id^" already defined.")
    with Not_found -> () in
  Environ.push_named d env

let push_named_def (id,de) senv =
  let (c,typ,cst) = Term_typing.translate_local_def senv.env de in
  let senv' = add_constraints cst senv in
  let env'' = safe_push_named (id,Some c,typ) senv'.env in
  (cst, {senv' with env=env''})

let push_named_assum (id,t) senv =
  let (t,cst) = Term_typing.translate_local_assum senv.env t in
  let senv' = add_constraints cst senv in
  let env'' = safe_push_named (id,None,t) senv'.env in
  (cst, {senv' with env=env''})


(* Insertion of constants and parameters in environment. *)

type global_declaration =
  | ConstantEntry of constant_entry
  | GlobalRecipe of Cooking.recipe

let add_constant dir l decl senv =
  let kn = make_con senv.modinfo.modpath dir l in
  let cb = match decl with
    | ConstantEntry ce -> Term_typing.translate_constant senv.env ce
    | GlobalRecipe r ->
      let cb = Term_typing.translate_recipe senv.env r in
      if DirPath.is_empty dir then Declareops.hcons_const_body cb else cb
  in
  let cb = match cb.const_body with
    | OpaqueDef lc when DirPath.is_empty dir ->
      (* In coqc, opaque constants outside sections will be stored
         indirectly in a specific table *)
      { cb with const_body = OpaqueDef (Lazyconstr.turn_indirect lc) }
    | _ -> cb
  in
  let senv' = add_field (l,SFBconst cb) (C kn) senv in
  let senv'' = match cb.const_body with
    | Undef (Some lev) ->
      update_resolver (add_inline_delta_resolver (user_con kn) (lev,None)) senv'
    | _ -> senv'
  in
  kn, senv''

(* Insertion of inductive types. *)

let add_mind dir l mie senv =
  let () = match mie.mind_entry_inds with
  | [] ->
    anomaly (Pp.str "empty inductive types declaration")
            (* this test is repeated by translate_mind *)
  | _ -> ()
  in
  let id = (List.nth mie.mind_entry_inds 0).mind_entry_typename in
  if not (Label.equal l (Label.of_id id)) then
    anomaly (Pp.str "the label of inductive packet and its first inductive \
	     type do not match");
  let kn = make_mind senv.modinfo.modpath dir l in
  let mib = Term_typing.translate_mind senv.env kn mie in
  let mib = match mib.mind_hyps with [] -> Declareops.hcons_mind mib | _ -> mib
  in
  let senv' = add_field (l,SFBmind mib) (I kn) senv in
  kn, senv'

(* Insertion of module types *)

let add_modtype l mte inl senv =
  let mp = MPdot(senv.modinfo.modpath, l) in
  let mtb = translate_module_type senv.env mp inl mte  in
  let senv' = add_field (l,SFBmodtype mtb) (MT mp) senv in
  mp, senv'

(* full_add_module adds module with universes and constraints *)
let full_add_module mb senv =
  let senv = add_constraints mb.mod_constraints senv in
  { senv with env = Modops.add_module mb senv.env }

(* Insertion of modules *)

let add_module l me inl senv =
  let mp = MPdot(senv.modinfo.modpath, l) in
  let mb = translate_module senv.env mp inl me in
  let senv' = add_field (l,SFBmodule mb) M senv in
  let senv'' = match mb.mod_type with
    | SEBstruct _ -> update_resolver (add_delta_resolver mb.mod_delta) senv'
    | _ -> senv'
  in
  mp,mb.mod_delta,senv''

(* Interactive modules *)

let start_module l senv =
  check_modlabel l senv;
 let mp = MPdot(senv.modinfo.modpath, l) in
 let modinfo = { modpath = mp;
		 label = l;
		 variant = STRUCT [];
		 resolver = empty_delta_resolver;
		 resolver_of_param = empty_delta_resolver}
 in
   mp, { old = senv;
	 env = senv.env;
	 modinfo = modinfo;
	 modlabels = Label.Set.empty;
	 objlabels = Label.Set.empty;
	 revstruct = [];
         univ = Univ.empty_constraint;
         engagement = None;
	 imports = senv.imports;
	 loads = [];
	 (* spiwack : not sure, but I hope it's correct *)
         local_retroknowledge = [] }

let end_module l restype senv =
  let oldsenv = senv.old in
  let modinfo = senv.modinfo in
  let mp = senv.modinfo.modpath in
  let restype =
    Option.map
      (fun (res,inl) -> translate_module_type senv.env mp inl res) restype in
  let params,is_functor =
    match modinfo.variant with
      | NONE | LIBRARY _ | SIG _ -> error_no_module_to_end ()
      | STRUCT params -> params, (List.length params > 0)
  in
  if not (Label.equal l modinfo.label) then error_incompatible_labels l modinfo.label;
  if not (empty_context senv.env) then error_non_empty_local_context None;
  let functorize_struct tb =
    List.fold_left
      (fun mtb (arg_id,arg_b) ->
	SEBfunctor(arg_id,arg_b,mtb))
      tb
      params
  in
   let auto_tb =
     SEBstruct (List.rev senv.revstruct)
  in
   let mexpr,mod_typ,mod_typ_alg,resolver,cst = 
    match restype with
      | None ->  let mexpr = functorize_struct auto_tb in
	 mexpr,mexpr,None,modinfo.resolver,empty_constraint
      | Some mtb ->
	  let auto_mtb = {
	    typ_mp = senv.modinfo.modpath;
	    typ_expr = auto_tb;
	    typ_expr_alg = None;
	    typ_constraints = empty_constraint;
	    typ_delta = empty_delta_resolver} in
	  let cst = check_subtypes senv.env auto_mtb
	    mtb in
	  let mod_typ = functorize_struct mtb.typ_expr in
	  let mexpr = functorize_struct auto_tb in
	  let typ_alg = 
	    Option.map functorize_struct mtb.typ_expr_alg in
	    mexpr,mod_typ,typ_alg,mtb.typ_delta,cst
  in
  let cst = union_constraints cst senv.univ in
  let mb =
    { mod_mp = mp;
      mod_expr = Some mexpr;
      mod_type = mod_typ;
      mod_type_alg = mod_typ_alg;
      mod_constraints = cst;
      mod_delta = resolver;
      mod_retroknowledge = senv.local_retroknowledge }
  in
  let newenv = oldsenv.env in
  let newenv = set_engagement_opt senv.engagement newenv in
  let senv'= {senv with env=newenv} in
  let senv' =
    List.fold_left
      (fun env (_,mb) -> full_add_module mb env) 
      senv'
      (List.rev senv'.loads)
  in
  let newenv = Environ.add_constraints cst senv'.env in
  let newenv =
    Modops.add_module mb newenv in 
  let modinfo = match mb.mod_type with
      SEBstruct _ -> 
	{ oldsenv.modinfo with
	    resolver = 
	    add_delta_resolver resolver oldsenv.modinfo.resolver}
    | _ -> oldsenv.modinfo
  in
    mp,resolver,{ old = oldsenv.old;
		  env = newenv;
		  modinfo = modinfo;
		  modlabels = Label.Set.add l oldsenv.modlabels;
		  objlabels = oldsenv.objlabels;
		  revstruct = (l,SFBmodule mb)::oldsenv.revstruct;
		  univ = Univ.union_constraints senv'.univ oldsenv.univ;
		  (* engagement is propagated to the upper level *)
		  engagement = senv'.engagement;
		  imports = senv'.imports;
		  loads = senv'.loads@oldsenv.loads;
		  local_retroknowledge =
	senv'.local_retroknowledge@oldsenv.local_retroknowledge }


(* Include for module and module type*)
 let add_include me is_module inl senv =
   let sign,cst,resolver =
     if is_module then
       let sign,_,resolver,cst =
	 translate_struct_include_module_entry senv.env
	   senv.modinfo.modpath inl me in
	 sign,cst,resolver
     else
       let mtb = 
	 translate_module_type senv.env 
	   senv.modinfo.modpath inl me in
       mtb.typ_expr,mtb.typ_constraints,mtb.typ_delta
   in
   let senv = add_constraints cst senv in
   let mp_sup = senv.modinfo.modpath in
     (* Include Self support  *)
   let rec compute_sign sign mb resolver senv = 
     match sign with
     | SEBfunctor(mbid,mtb,str) ->
	 let cst_sub = check_subtypes senv.env mb mtb in
	 let senv = add_constraints cst_sub senv in
	 let mpsup_delta =
	   inline_delta_resolver senv.env inl mp_sup mbid mtb mb.typ_delta
	 in
	 let subst = map_mbid mbid mp_sup mpsup_delta in
	 let resolver = subst_codom_delta_resolver subst resolver in
	   (compute_sign 
	     (subst_struct_expr subst str) mb resolver senv)
     | str -> resolver,str,senv
   in
   let resolver,sign,senv = compute_sign sign {typ_mp = mp_sup;
				      typ_expr = SEBstruct (List.rev senv.revstruct);
				      typ_expr_alg = None;
				      typ_constraints = empty_constraint;
				      typ_delta = senv.modinfo.resolver} resolver senv
   in
   let str = match sign with
     | SEBstruct(str_l) -> str_l
     | _ -> error ("You cannot Include a higher-order structure.")
   in
   let senv = update_resolver (add_delta_resolver resolver) senv
   in
   let add senv ((l,elem) as field) =
     let new_name = match elem with
       | SFBconst _ ->
           C (constant_of_delta_kn resolver (KerName.make2 mp_sup l))
       | SFBmind _ ->
	   I (mind_of_delta_kn resolver (KerName.make2 mp_sup l))
       | SFBmodule _ -> M
       | SFBmodtype _ -> MT (MPdot(senv.modinfo.modpath, l))
     in
     add_field field new_name senv
   in
   resolver,(List.fold_left add senv str)

(* Adding parameters to modules or module types *)

let add_module_parameter mbid mte inl senv =
  let () = match senv.revstruct, senv.loads with
  | [], _ :: _ | _ :: _, [] ->
    anomaly (Pp.str "Cannot add a module parameter to a non empty module")
  | _ -> ()
  in
  let mp = MPbound mbid in
  let mtb = translate_module_type senv.env mp inl mte in
  let senv = full_add_module (module_body_of_type mp mtb) senv
  in
  let new_variant = match senv.modinfo.variant with
    | STRUCT params -> STRUCT ((mbid,mtb) :: params)
    | SIG params -> SIG ((mbid,mtb) :: params)
    | _ ->
      let msg = "Module parameters can only be added to modules or signatures"
      in anomaly (Pp.str msg)
  in

  let resolver_of_param = match mtb.typ_expr with
      SEBstruct _ -> mtb.typ_delta
    | _ -> empty_delta_resolver
  in
    mtb.typ_delta, { old = senv.old;
		     env = senv.env;
		     modinfo = { senv.modinfo with 
				   variant = new_variant;
				   resolver_of_param = add_delta_resolver
			      resolver_of_param senv.modinfo.resolver_of_param};
		     modlabels = senv.modlabels;
		     objlabels = senv.objlabels;
		     revstruct = [];
		     univ = senv.univ;
		     engagement = senv.engagement;
		     imports = senv.imports;
		     loads = [];
		     local_retroknowledge = senv.local_retroknowledge }
      

(* Interactive module types *)

let start_modtype l senv =
  check_modlabel l senv;
 let mp = MPdot(senv.modinfo.modpath, l) in
 let modinfo = { modpath = mp;
		 label = l;
		 variant = SIG [];
		 resolver = empty_delta_resolver;
		 resolver_of_param = empty_delta_resolver}
 in
  mp, { old = senv;
	env = senv.env;
	modinfo = modinfo;
	modlabels = Label.Set.empty;
	objlabels = Label.Set.empty;
	revstruct = [];
        univ = Univ.empty_constraint;
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
  if not (Label.equal l modinfo.label) then error_incompatible_labels l modinfo.label;
  if not (empty_context senv.env) then error_non_empty_local_context None;
  let auto_tb =
     SEBstruct (List.rev senv.revstruct)
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
  let newenv = Environ.add_constraints senv.univ  newenv in
  let newenv = set_engagement_opt senv.engagement newenv in
  let senv = {senv with env=newenv} in
  let senv =
    List.fold_left
      (fun env (mp,mb) -> full_add_module mb env)
      senv
      (List.rev senv.loads)
  in
  let mtb = {typ_mp = mp;
    typ_expr = mtb_expr;
    typ_expr_alg = None;
    typ_constraints = senv.univ;
    typ_delta = senv.modinfo.resolver} in
  let newenv =
    Environ.add_modtype mp mtb senv.env
  in
    mp, { old = oldsenv.old;
	  env = newenv;
	  modinfo = oldsenv.modinfo;
	  modlabels = Label.Set.add l oldsenv.modlabels;
	  objlabels = oldsenv.objlabels;
	  revstruct = (l,SFBmodtype mtb)::oldsenv.revstruct;
          univ = Univ.union_constraints senv.univ oldsenv.univ;
          engagement = senv.engagement;
	  imports = senv.imports;
	  loads = senv.loads@oldsenv.loads;
          (* spiwack : if there is a bug with retroknowledge in nested modules
             it's likely to come from here *)
          local_retroknowledge = 
        senv.local_retroknowledge@oldsenv.local_retroknowledge}

let delta_of_senv senv = senv.modinfo.resolver,senv.modinfo.resolver_of_param

(* Check that the engagement expected by a library matches the initial one *)
let check_engagement env c =
  match Environ.engagement env, c with
    | Some ImpredicativeSet, Some ImpredicativeSet -> ()
    | _, None -> ()
    | _, Some ImpredicativeSet ->
        error "Needs option -impredicative-set."

let set_engagement c senv =
  {senv with
    env = Environ.set_engagement c senv.env;
    engagement = Some c }

(* Libraries = Compiled modules *)

type compiled_library = {
  comp_name : DirPath.t;
  comp_mod : module_body;
  comp_deps : library_info array;
  comp_enga : engagement option;
  comp_natsymbs : Nativecode.symbol array
}

type native_library = Nativecode.global list

(* We check that only initial state Require's were performed before
   [start_library] was called *)

let is_empty senv = match senv.revstruct, senv.modinfo.variant with
  | [], NONE -> mp_eq senv.modinfo.modpath initial_path
  | _ -> false

let start_library dir senv =
  if not (is_empty senv) then
    anomaly ~label:"Safe_typing.start_library" (Pp.str "environment should be empty");
  let dir_path,l =
    match (DirPath.repr dir) with
	[] -> anomaly (Pp.str "Empty dirpath in Safe_typing.start_library")
      | hd::tl ->
	  DirPath.make tl, Label.of_id hd
  in
  let mp = MPfile dir in
  let modinfo = {modpath = mp;
		 label = l;
		 variant = LIBRARY dir;
		 resolver = empty_delta_resolver;
		 resolver_of_param = empty_delta_resolver}
  in
  mp, { old = senv;
	env = senv.env;
	modinfo = modinfo;
	modlabels = Label.Set.empty;
	objlabels = Label.Set.empty;
	revstruct = [];
        univ = Univ.empty_constraint;
        engagement = None;
	imports = senv.imports;
	loads = [];
        local_retroknowledge = [] }

let export senv dir =
  let modinfo = senv.modinfo in
  begin
    match modinfo.variant with
      | LIBRARY dp ->
	  if not (DirPath.equal dir dp) then
	    anomaly (Pp.str "We are not exporting the right library!")
      | _ ->
	  anomaly (Pp.str "We are not exporting the library")
  end;
  (*if senv.modinfo.params <> [] || senv.modinfo.restype <> None then
    (* error_export_simple *) (); *)
    let str = SEBstruct (List.rev senv.revstruct) in
    let mp = senv.modinfo.modpath in
    let mb = 
    { mod_mp = mp;
      mod_expr = Some str;
      mod_type = str;
      mod_type_alg = None;
      mod_constraints = senv.univ;
      mod_delta = senv.modinfo.resolver;
      mod_retroknowledge = senv.local_retroknowledge
    }
  in
  let ast, values =
    if !Flags.no_native_compiler then [], [||]
    else let ast, values, upds = Nativelibrary.dump_library mp dir senv.env str in
    Nativecode.update_locations upds;
    ast, values
  in
  let lib = {
    comp_name = dir;
    comp_mod = mb;
    comp_deps = Array.of_list senv.imports;
    comp_enga = engagement senv.env;
    comp_natsymbs = values }
  in
  mp, lib, ast

let check_imports senv needed =
  let imports = senv.imports in
  let check (id,stamp) =
    try
      let actual_stamp = List.assoc id imports in
      if not (String.equal stamp actual_stamp) then
	error
	  ("Inconsistent assumptions over module "^(DirPath.to_string id)^".")
    with Not_found ->
      error ("Reference to unknown module "^(DirPath.to_string id)^".")
  in
  Array.iter check needed



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

let import lib digest senv =
  check_imports senv lib.comp_deps;
  check_engagement senv.env lib.comp_enga;
  let mp = MPfile lib.comp_name in
  let mb = lib.comp_mod in
  let env = senv.env in
  let env = Environ.add_constraints mb.mod_constraints env in
  let env = Modops.add_module mb env in
  let reso = add_delta_resolver mb.mod_delta senv.modinfo.resolver in
  let senv = { senv with
    env = env;
    modinfo = { senv.modinfo with resolver = reso };
    imports = (lib.comp_name,digest)::senv.imports;
    loads = (mp,mb)::senv.loads }
  in
  mp, senv, lib.comp_natsymbs


type judgment = unsafe_judgment

let j_val j = j.uj_val
let j_type j = j.uj_type

let safe_infer senv = infer (env_of_senv senv)

let typing senv = Typeops.typing (env_of_senv senv)

(* This function serves only for inlining constants in native compiler for now,
but it is meant to become a replacement for environ.register *)
let register_inline kn senv =
  if not (evaluable_constant kn senv.env) then
    Errors.error "Register inline: an evaluable constant is expected";
  let env = pre_env senv.env in
  let (cb,r) = Cmap_env.find kn env.Pre_env.env_globals.Pre_env.env_constants in
  let cb = {cb with const_inline_code = true} in 
  let new_constants =
    Cmap_env.add kn (cb,r) env.Pre_env.env_globals.Pre_env.env_constants
  in
  let new_globals = { env.Pre_env.env_globals with Pre_env.env_constants = new_constants } in
  let env = { env with Pre_env.env_globals = new_globals } in
  { senv with env = env_of_pre_env env }
