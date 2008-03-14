(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Pp
open Util
open Names
open Declarations
open Entries
open Libnames
open Libobject
open Lib
open Nametab
open Mod_subst

(* modules and components *)


(* This type is a functional closure of substitutive lib_objects.

   The first part is a partial substitution (which will be later
   applied to lib_objects when completed).

   The second one is a list of bound identifiers which is nonempty
   only if the objects are owned by a fuctor

   The third one is the "self" ident of the signature (or structure),
   which should be substituted in lib_objects with the real name of
   the module.

   The fourth one is the segment itself which can contain references
   to identifiers in the domain of the substitution or in other two
   parts. These references are invalid in the current scope and
   therefore must be substitued with valid names before use.

*)
type substitutive_objects = 
    substitution * mod_bound_id list * mod_self_id * lib_objects


(* For each module, we store the following things:

   In modtab_substobjs: substitutive_objects 
     when we will do Module M:=N, the objects of N will be reloaded 
     with M after substitution

   In modtab_objects: "substituted objects" @ "keep objects"

   substituted objects - 
     roughly the objects above after the substitution - we need to 
     keep them to call open_object when the module is opened (imported)
 
   keep objects -
     The list of non-substitutive objects - as above, for each of 
     them we will call open_object when the module is opened 
     
   (Some) Invariants:
   * If the module is a functor, the two latter lists are empty.

   * Module objects in substitutive_objects part have empty substituted 
     objects.

   * Modules which where created with Module M:=mexpr or with 
     Module M:SIG. ... End M. have the keep list empty.
*)
let modtab_substobjs = 
  ref (MPmap.empty : substitutive_objects MPmap.t)
let modtab_objects = 
  ref (MPmap.empty : (object_prefix * lib_objects) MPmap.t)


(* currently started interactive module (if any) - its arguments (if it
   is a functor) and declared output type *)
let openmod_info = 
  ref (([],None,None) : mod_bound_id list * module_type_entry option 
                                          * module_type_body option) 

let _ = Summary.declare_summary "MODULE-INFO"
	  { Summary.freeze_function = (fun () -> 
					 !modtab_substobjs,
					 !modtab_objects,
					 !openmod_info);
	    Summary.unfreeze_function = (fun (sobjs,objs,info) -> 
					   modtab_substobjs := sobjs;
					   modtab_objects := objs;
					   openmod_info := info);
	    Summary.init_function = (fun () -> 
				       modtab_substobjs := MPmap.empty;
				       modtab_objects := MPmap.empty;
				       openmod_info := ([],None,None));
	    Summary.survive_module = false;
	    Summary.survive_section = false }

(* auxiliary functions to transform section_path and kernel_name given
   by Lib into module_path and dir_path needed for modules *)

let mp_of_kn kn = 
  let mp,sec,l = repr_kn kn in 
    if sec=empty_dirpath then 
      MPdot (mp,l) 
    else
      anomaly ("Non-empty section in module name!" ^ string_of_kn kn)

let dir_of_sp sp = 
  let dir,id = repr_path sp in
    extend_dirpath dir id

let msid_of_mp = function
    MPself msid -> msid
  | _ -> anomaly "'Self' module path expected!"

let msid_of_prefix (_,(mp,sec)) = 
  if sec=empty_dirpath then 
    msid_of_mp mp
  else
    anomaly ("Non-empty section in module name!" ^ 
	     string_of_mp mp ^ "." ^ string_of_dirpath sec)

(* Check that a module type is not functorial *)

let rec check_sig env = function
  | MTBident kn -> check_sig env (Environ.lookup_modtype kn env)
  | MTBsig _ -> ()
  | MTBfunsig _ -> Modops.error_result_must_be_signature ()

let rec check_sig_entry env = function
  | MTEident kn -> check_sig env (Environ.lookup_modtype kn env)
  | MTEfunsig _ -> Modops.error_result_must_be_signature ()
  | MTEwith (mte,_) -> check_sig_entry env mte

(* This function checks if the type calculated for the module [mp] is
   a subtype of [sub_mtb]. Uses only the global environment. *)
let check_subtypes mp sub_mtb =
  let env = Global.env () in
  let mtb = (Environ.lookup_module mp env).mod_type in
  let _ = Environ.add_constraints 
	    (Subtyping.check_subtypes env mtb sub_mtb) 
  in
    ()  (* The constraints are checked and forgot immediately! *) 


(* This function registers the visibility of the module and iterates
   through its components. It is called by plenty module functions *)

let do_module exists what iter_objects i dir mp substobjs objects =
  let prefix = (dir,(mp,empty_dirpath)) in
  let dirinfo = DirModule (dir,(mp,empty_dirpath)) in
  let vis = 
    if exists then 
      if 
	try Nametab.locate_dir (qualid_of_dirpath dir) = dirinfo 
	with Not_found -> false 
      then
	Nametab.Exactly i
      else
	errorlabstrm (what^"_module") 
	  (pr_dirpath dir ++ str " should already exist!") 
    else
      if Nametab.exists_dir dir then
	errorlabstrm (what^"_module") (pr_dirpath dir ++ str " already exists")
      else
	Nametab.Until i
  in
    Nametab.push_dir vis dir dirinfo;
    modtab_substobjs := MPmap.add mp substobjs !modtab_substobjs;
    match objects with
	Some seg -> 
	  modtab_objects := MPmap.add mp (prefix,seg) !modtab_objects;
	  iter_objects (i+1) prefix seg	  
      | None ->  ()

    
let conv_names_do_module exists what iter_objects i 
      (sp,kn) substobjs substituted =
  let dir,mp = dir_of_sp sp, mp_of_kn kn in
  do_module exists what iter_objects i dir mp substobjs substituted

(* Interactive modules and module types cannot be recached! cache_mod*
   functions can be called only once (and "end_mod*" set the flag to
   false then)
*)

let cache_module ((sp,kn as oname),(entry,substobjs,substituted)) =
  let _ = match entry with
    | None ->
	anomaly "You must not recache interactive modules!"
    | Some (me,sub_mte_o) ->
	let sub_mtb_o = match sub_mte_o with 
	    None -> None
	  | Some mte -> Some (Mod_typing.translate_modtype (Global.env()) mte)
	in

	let mp = Global.add_module (basename sp) me in
	if mp <> mp_of_kn kn then
	  anomaly "Kernel and Library names do not match";
	  
	match sub_mtb_o with
	    None -> ()
	  | Some sub_mtb -> 
check_subtypes mp sub_mtb

  in
  conv_names_do_module false "cache" load_objects 1 oname substobjs substituted


(* TODO: This check is not essential *)
let check_empty s = function
     | None -> ()
     | Some _ -> 
	 anomaly ("We should never have full info in " ^ s^"!")


(* When this function is called the module itself is already in the
   environment. This function loads its objects only *)

let load_module i (oname,(entry,substobjs,substituted)) =
  (* TODO: This check is not essential *)
  check_empty "load_module" entry;
  conv_names_do_module false "load" load_objects i oname substobjs substituted


let open_module i (oname,(entry,substobjs,substituted)) =
  (* TODO: This check is not essential *)
  check_empty "open_module" entry;
  conv_names_do_module true "open" open_objects i oname substobjs substituted


let subst_substobjs dir mp (subst,mbids,msid,objs) =
  match mbids with
    | [] -> 
	let prefix = dir,(mp,empty_dirpath) in
	  Some (subst_objects prefix (add_msid msid mp subst) objs)
    | _ -> None


let subst_module ((sp,kn),subst,(entry,substobjs,_)) =
  check_empty "subst_module" entry;
  let dir,mp = dir_of_sp sp, mp_of_kn kn in
  let (sub,mbids,msid,objs) = substobjs in
  let subst' = join sub subst in
  (* substitutive_objects get the new substitution *)
  let substobjs = (subst',mbids,msid,objs) in
  (* if we are not a functor - calculate substitued.
     We add "msid |-> mp" to the substitution *)
  let substituted = subst_substobjs dir mp substobjs
  in
    (None,substobjs,substituted)


let classify_module (_,(_,substobjs,_)) =
  Substitute (None,substobjs,None)

let (in_module,out_module) =
  declare_object {(default_object "MODULE") with
    cache_function = cache_module;
    load_function = load_module;
    open_function = open_module;
    subst_function = subst_module;
    classify_function = classify_module;
    export_function = (fun _ -> anomaly "No modules in sections!") }


let cache_keep _ = anomaly "This module should not be cached!"

let load_keep i ((sp,kn),seg) = 
  let mp = mp_of_kn kn in
  let prefix = dir_of_sp sp, (mp,empty_dirpath) in
    begin 
      try
	let prefix',objects = MPmap.find mp !modtab_objects in
	  if prefix' <> prefix then 
	    anomaly "Two different modules with the same path!";
	  modtab_objects := MPmap.add mp (prefix,objects@seg) !modtab_objects;
      with
	  Not_found -> anomaly "Keep objects before substitutive"
    end;
    load_objects i prefix seg

let open_keep i ((sp,kn),seg) = 
  let dirpath,mp = dir_of_sp sp, mp_of_kn kn in
    open_objects i (dirpath,(mp,empty_dirpath)) seg

let (in_modkeep,out_modkeep) = 
  declare_object {(default_object "MODULE KEEP OBJECTS") with
    cache_function = cache_keep;
    load_function = load_keep;
    open_function = open_keep;
    export_function = (fun _ -> anomaly "No modules in sections!") }

(* we remember objects for a module type. In case of a declaration:
   Module M:SIG:=...
   The module M gets its objects from SIG
*)
let modtypetab =
  ref (KNmap.empty : substitutive_objects KNmap.t)

(* currently started interactive module type. We remember its arguments
   if it is a functor type *)
let openmodtype_info =
  ref ([] : mod_bound_id list)

let _ = Summary.declare_summary "MODTYPE-INFO"
	  { Summary.freeze_function = (fun () ->
					 !modtypetab,!openmodtype_info);
	    Summary.unfreeze_function = (fun ft ->
					   modtypetab := fst ft;
					   openmodtype_info := snd ft);
	    Summary.init_function = (fun () ->
				       modtypetab := KNmap.empty;
				       openmodtype_info := []);
	    Summary.survive_module = false;
	    Summary.survive_section = true }




let cache_modtype ((sp,kn),(entry,modtypeobjs)) =
  let _ = 
    match entry with
      | None ->
	  anomaly "You must not recache interactive module types!"
      | Some mte ->
	  let kn' = Global.add_modtype (basename sp) mte in
	  if kn' <> kn then
	    anomaly "Kernel and Library names do not match"
  in

  if Nametab.exists_modtype sp then
    errorlabstrm "cache_modtype"
      (pr_sp sp ++ str " already exists") ;

  Nametab.push_modtype (Nametab.Until 1) sp kn;

  modtypetab := KNmap.add kn modtypeobjs !modtypetab


let load_modtype i ((sp,kn),(entry,modtypeobjs)) =
  check_empty "load_modtype" entry;

  if Nametab.exists_modtype sp then
    errorlabstrm "cache_modtype"
      (pr_sp sp ++ str " already exists") ;

  Nametab.push_modtype (Nametab.Until i) sp kn;
    
  modtypetab := KNmap.add kn modtypeobjs !modtypetab


let open_modtype i ((sp,kn),(entry,_)) =
  check_empty "open_modtype" entry;

  if 
    try Nametab.locate_modtype (qualid_of_sp sp) <> kn 
    with Not_found -> true
  then
    errorlabstrm ("open_modtype") 
      (pr_sp sp ++ str " should already exist!");

  Nametab.push_modtype (Nametab.Exactly i) sp kn


let subst_modtype (_,subst,(entry,(subs,mbids,msid,objs))) =
  check_empty "subst_modtype" entry;
  (entry,(join subs subst,mbids,msid,objs))


let classify_modtype (_,(_,substobjs)) =
  Substitute (None,substobjs)


let (in_modtype,out_modtype) =
    declare_object {(default_object "MODULE TYPE") with
      cache_function = cache_modtype;
      open_function = open_modtype;
      load_function = load_modtype;
      subst_function = subst_modtype;
      classify_function = classify_modtype;
      export_function = Option.make }



let rec replace_module_object idl (subst, mbids, msid, lib_stack) modobjs =
  if mbids<>[] then 
    error "Unexpected functor objects"
  else
    let rec replace_idl = function 
      | _,[] -> [] 
      | id::idl,(id',obj)::tail when id = id' ->
	  if object_tag obj = "MODULE" then
           (match idl with
               [] -> (id, in_module (None,modobjs,None))::tail
             | _ ->
               let (_,substobjs,_) = out_module obj in
                let substobjs' = replace_module_object idl substobjs modobjs in
                 (id, in_module (None,substobjs',None))::tail
           )
	  else error "MODULE expected!"
      | idl,lobj::tail -> lobj::replace_idl (idl,tail)
    in
      (subst, mbids, msid, replace_idl (idl,lib_stack))

let abstract_substobjs mbids1 (subst, mbids2, msid, lib_stack) =
  (subst, mbids1@mbids2, msid, lib_stack)


let rec get_modtype_substobjs = function
    MTEident ln -> KNmap.find ln !modtypetab
  | MTEfunsig (mbid,_,mte) ->
      let (subst, mbids, msid, objs) = get_modtype_substobjs mte in
	(subst, mbid::mbids, msid, objs)
  | MTEwith (mty, With_Definition _) -> get_modtype_substobjs mty
  | MTEwith (mty, With_Module (idl,mp)) -> 
      let substobjs = get_modtype_substobjs mty in
      let modobjs = MPmap.find mp !modtab_substobjs in
	replace_module_object idl substobjs modobjs
 
(* push names of bound modules (and their components) to Nametab *)
(* add objects associated to them *)
let process_module_bindings argids args =
  let process_arg id (mbid,mty) =
    let dir = make_dirpath [id] in
    let mp = MPbound mbid in
    let substobjs = get_modtype_substobjs mty in
    let substituted = subst_substobjs dir mp substobjs in
      do_module false "start" load_objects 1 dir mp substobjs substituted
  in
    List.iter2 process_arg argids args


let replace_module mtb id mb = todo "replace module after with"; mtb 

let rec get_some_body mty env = match mty with
    MTEident kn -> Environ.lookup_modtype kn env 
  | MTEfunsig _ -> anomaly "anonymous module types not supported"
  | MTEwith (mty,With_Definition _) -> get_some_body mty env 
  | MTEwith (mty,With_Module (id,mp)) -> 
      replace_module (get_some_body mty env) id (Environ.lookup_module mp env)


let intern_args interp_modtype (idl,arg) = 
  let lib_dir = Lib.library_dp() in
  let mbids = List.map (fun (_,id) -> make_mbid lib_dir (string_of_id id)) idl in
  let mty = interp_modtype (Global.env()) arg in
  let dirs = List.map (fun (_,id) -> make_dirpath [id]) idl in
  let substobjs = get_modtype_substobjs mty in
  List.map2
    (fun dir mbid -> 
      Global.add_module_parameter mbid mty;
      let mp = MPbound mbid in
      let substituted = subst_substobjs dir mp substobjs in
      do_module false "interp" load_objects 1 dir mp substobjs substituted;
      (mbid,mty))
    dirs mbids

let start_module interp_modtype export id args res_o =
  let fs = Summary.freeze_summaries () in

  let mp = Global.start_module id in
  let arg_entries = List.concat (List.map (intern_args interp_modtype) args) in

  let res_entry_o, sub_body_o = match res_o with
      None -> None, None
    | Some (res, restricted) ->
	(* we translate the module here to catch errors as early as possible *)
	let mte = interp_modtype (Global.env()) res in
	check_sig_entry (Global.env()) mte;
	if restricted then
	  Some mte, None
	else
	  let mtb = Mod_typing.translate_modtype (Global.env()) mte in
	  let sub_mtb = 
	    List.fold_right 
	      (fun (arg_id,arg_t) mte -> 
		let arg_t = Mod_typing.translate_modtype (Global.env()) arg_t
		in MTBfunsig(arg_id,arg_t,mte))
	      arg_entries mtb
	  in
	  None, Some sub_mtb
  in

  let mbids = List.map fst arg_entries in
  openmod_info:=(mbids,res_entry_o,sub_body_o);
  let prefix = Lib.start_module export id mp fs in
  Nametab.push_dir (Nametab.Until 1) (fst prefix) (DirOpenModule prefix);
  Lib.add_frozen_state ()


let end_module id =

  let oldoname,oldprefix,fs,lib_stack = Lib.end_module id in
  let mbids, res_o, sub_o = !openmod_info in
  let mp = Global.end_module id res_o in
    
  begin match sub_o with
      None -> ()
    | Some sub_mtb -> check_subtypes mp sub_mtb
  end;
    
  let substitute, keep, special = Lib.classify_segment lib_stack in

  let dir = fst oldprefix in
  let msid = msid_of_prefix oldprefix in

  let substobjs, keep, special = try
    match res_o with
      | None -> 
	  (empty_subst, mbids, msid, substitute), keep, special
      | Some (MTEident ln) ->
	  abstract_substobjs mbids (KNmap.find ln (!modtypetab)), [], []
      | Some (MTEwith _ as mty) ->
	  abstract_substobjs mbids (get_modtype_substobjs mty), [], []
      | Some (MTEfunsig _) -> 
	  anomaly "Funsig cannot be here..."
    with
	Not_found -> anomaly "Module objects not found..."
  in

  (* must be called after get_modtype_substobjs, because of possible
     dependencies on functor arguments *)
  Summary.module_unfreeze_summaries fs;

  let substituted = subst_substobjs dir mp substobjs in
  let node = in_module (None,substobjs,substituted) in
  let objects = 
    if keep = [] || mbids <> [] then 
      special@[node]   (* no keep objects or we are defining a functor *)
    else
      special@[node;in_modkeep keep]   (* otherwise *)
  in
  let newoname = Lib.add_leaves id objects in

    if (fst newoname) <> (fst oldoname) then
      anomaly "Names generated on start_ and end_module do not match";
    if mp_of_kn (snd newoname) <> mp then 
      anomaly "Kernel and Library names do not match";

    Lib.add_frozen_state () (* to prevent recaching *)



let module_objects mp = 
  let prefix,objects = MPmap.find mp !modtab_objects in
    segment_of_objects prefix objects



(************************************************************************)
(* libraries *)

type library_name = dir_path

(* The first two will form substitutive_objects, the last one is keep *)
type library_objects = 
    mod_self_id * lib_objects * lib_objects


(* The library_cache here is needed to avoid recalculations of
   substituted modules object during "reloading" of libraries *)
let library_cache = Hashtbl.create 17


let register_library dir cenv objs digest =
  let mp = MPfile dir in
  let substobjs, objects =
    try 
      ignore(Global.lookup_module mp);
      (* if it's in the environment, the cached objects should be correct *)
      Hashtbl.find library_cache dir
    with
	Not_found ->
	  if mp <> Global.import cenv digest then
	    anomaly "Unexpected disk module name";
	  let msid,substitute,keep = objs in
	  let substobjs = empty_subst, [], msid, substitute in
	  let substituted = subst_substobjs dir mp substobjs in
	  let objects = Option.map (fun seg -> seg@keep) substituted in
	  let modobjs = substobjs, objects in
	    Hashtbl.add library_cache dir modobjs;
	    modobjs
  in
    do_module false "register_library" load_objects 1 dir mp substobjs objects


let start_library dir = 
  let mp = Global.start_library dir in
  openmod_info:=[],None,None;
  Lib.start_compilation dir mp;
  Lib.add_frozen_state ()


let end_library dir = 
  let prefix, lib_stack = Lib.end_compilation dir in
  let cenv = Global.export dir in
  let msid = msid_of_prefix prefix in
  let substitute, keep, _ = Lib.classify_segment lib_stack in
    cenv,(msid,substitute,keep)


(* implementation of Export M and Import M *)


let really_import_module mp = 
  let prefix,objects = MPmap.find mp !modtab_objects in
    open_objects 1 prefix objects


let cache_import (_,(_,mp)) = 
(* for non-substitutive exports: 
  let mp = Nametab.locate_module (qualid_of_dirpath dir) in  *)
  really_import_module mp

let classify_import (_,(export,_ as obj)) = 
  if export then Substitute obj else Dispose

let subst_import (_,subst,(export,mp as obj)) =
  let mp' = subst_mp subst mp in
    if mp'==mp then obj else
      (export,mp')

let (in_import,out_import) = 
  declare_object {(default_object "IMPORT MODULE") with
    cache_function = cache_import;
    open_function = (fun i o -> if i=1 then cache_import o);
    subst_function = subst_import;
    classify_function = classify_import }


let import_module export mp = 
  Lib.add_anonymous_leaf (in_import (export,mp))

(************************************************************************)
(* module types *)

let start_modtype interp_modtype id args =
  let fs = Summary.freeze_summaries () in

  let mp = Global.start_modtype id in
  let arg_entries = List.concat (List.map (intern_args interp_modtype) args) in

  let mbids = List.map fst arg_entries in
  openmodtype_info := mbids;
  let prefix = Lib.start_modtype id mp fs in
  Nametab.push_dir (Nametab.Until 1) (fst prefix) (DirOpenModtype prefix);
  Lib.add_frozen_state ()


let end_modtype id =

  let oldoname,prefix,fs,lib_stack = Lib.end_modtype id in
  let ln = Global.end_modtype id in
  let substitute, _, special = Lib.classify_segment lib_stack in

  let msid = msid_of_prefix prefix in
  let mbids = !openmodtype_info in

  Summary.module_unfreeze_summaries fs;

  let modtypeobjs = empty_subst, mbids, msid, substitute in

  let oname = Lib.add_leaves id (special@[in_modtype (None, modtypeobjs)]) in
  if fst oname <> fst oldoname then
    anomaly
      "Section paths generated on start_ and end_modtype do not match";
  if snd oname <> ln then
    anomaly
      "Kernel and Library names do not match";

  Lib.add_frozen_state ()(* to prevent recaching *)


let declare_modtype interp_modtype id args mty = 
  let fs = Summary.freeze_summaries () in

  try
  let _ = Global.start_modtype id in
  let arg_entries = List.concat (List.map (intern_args interp_modtype) args) in

  let base_mty = interp_modtype (Global.env()) mty in
  let entry = 
    List.fold_right 
      (fun (arg_id,arg_t) mte -> MTEfunsig(arg_id,arg_t,mte))
      arg_entries
      base_mty
  in
  let substobjs = get_modtype_substobjs entry in
  (* Undo the simulated interactive building of the module type *)
  (* and declare the module type as a whole *)
  Summary.unfreeze_summaries fs;
    
  ignore (add_leaf id (in_modtype (Some entry, substobjs)))
  with e ->
    (* Something wrong: undo the whole process *)
    Summary.unfreeze_summaries fs; raise e
			       

let rec get_module_substobjs env = function
  | MEident mp -> MPmap.find mp !modtab_substobjs 
  | MEfunctor (mbid,mty,mexpr) ->
       let (subst, mbids, msid, objs) = get_module_substobjs env mexpr in
	(subst, mbid::mbids, msid, objs)
  | MEapply (mexpr, MEident mp) ->
      let feb,ftb = Mod_typing.translate_mexpr env mexpr in
      let ftb = Modops.scrape_modtype env ftb in
      let farg_id, farg_b, fbody_b = Modops.destr_functor ftb in
      let (subst, mbids, msid, objs) = get_module_substobjs env mexpr in
	(match mbids with
	   | mbid::mbids ->
              let resolve =
               Modops.resolver_of_environment farg_id farg_b mp env in
               (* application outside the kernel, only for substitutive
                  objects (that are all non-logical objects) *)
	       (add_mbid mbid mp (Some resolve) subst, mbids, msid, objs)
	   | [] -> match mexpr with
	       | MEident _  -> error "Application of a non-functor"
	       | _ -> error "Application of a functor with too few arguments")
  | MEapply (_,mexpr) ->
      Modops.error_application_to_not_path mexpr


let declare_module interp_modtype interp_modexpr id args mty_o mexpr_o =

  let fs = Summary.freeze_summaries () in

  try
  let _ = Global.start_module id in
  let arg_entries = List.concat (List.map (intern_args interp_modtype) args) in

  let mty_entry_o, mty_sub_o = match mty_o with
      None -> None, None
    | (Some (mty, true)) -> 
	Some (List.fold_right 
		(fun (arg_id,arg_t) mte -> MTEfunsig(arg_id,arg_t,mte))
		arg_entries 
		(interp_modtype (Global.env()) mty)), 
	None
    | (Some (mty, false)) -> 
	None, 
	Some (List.fold_right 
		(fun (arg_id,arg_t) mte -> MTEfunsig(arg_id,arg_t,mte))
		arg_entries 
		(interp_modtype (Global.env()) mty))
  in
  let mexpr_entry_o = match mexpr_o with
      None -> None
    | Some mexpr -> 
	Some (List.fold_right 
		(fun (mbid,mte) me -> MEfunctor(mbid,mte,me))
		arg_entries
		(interp_modexpr (Global.env()) mexpr))
  in
  let entry = 
    {mod_entry_type = mty_entry_o;	    
     mod_entry_expr = mexpr_entry_o }
  in
  let env = Global.env() in
  let substobjs =
    match entry with
      | {mod_entry_type = Some mte} -> get_modtype_substobjs mte
      | {mod_entry_expr = Some mexpr} -> get_module_substobjs env mexpr
      | _ -> anomaly "declare_module: No type, no body ..."
  in

    (* Undo the simulated interactive building of the module *)
    (* and declare the module as a whole *)
    Summary.unfreeze_summaries fs;

    let dir,mp = dir_of_sp (Lib.make_path id), mp_of_kn (Lib.make_kn id) in
    let substituted = subst_substobjs dir mp substobjs in

      ignore (add_leaf
		id
		(in_module (Some (entry, mty_sub_o), substobjs, substituted)))

  with e -> 
    (* Something wrong: undo the whole process *)
    Summary.unfreeze_summaries fs; raise e


(*s Iterators. *)

let iter_all_segments f =
  let _ = 
    MPmap.iter 
      (fun _ (prefix,objects) -> 
	 let apply_obj (id,obj) = f (make_oname prefix id) obj in
	   List.iter apply_obj objects)
      !modtab_objects
  in
  let rec apply_node = function
    | sp, Leaf o -> f sp o
    | _ -> ()
  in
    List.iter apply_node (Lib.contents_after None)


let debug_print_modtab _ =
  let pr_seg = function
    | [] -> str "[]"
    | l -> str ("[." ^ string_of_int (List.length l) ^ ".]")
  in
  let pr_modinfo mp (prefix,objects) s =
    s ++ str (string_of_mp mp) ++ (spc ())
    ++ (pr_seg (segment_of_objects prefix objects))
  in
  let modules = MPmap.fold pr_modinfo !modtab_objects (mt ()) in
    hov 0 modules
