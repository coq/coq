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


(* OBSOLETE This type is a functional closure of substitutive lib_objects.

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
     mod_bound_id list * module_path * lib_objects


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
  ref ((MPfile(initial_dir),[],None,None) 
	 : module_path *  mod_bound_id list * module_struct_entry option 
                                          * module_type_body option) 

(* The library_cache here is needed to avoid recalculations of
   substituted modules object during "reloading" of libraries *)
let library_cache = ref Dirmap.empty

let _ = Summary.declare_summary "MODULE-INFO"
	  { Summary.freeze_function = (fun () ->
					 !modtab_substobjs,
					 !modtab_objects,
					 !openmod_info,
					 !library_cache);
	    Summary.unfreeze_function = (fun (sobjs,objs,info,libcache) ->
					   modtab_substobjs := sobjs;
					   modtab_objects := objs;
					   openmod_info := info;
					   library_cache := libcache);
	    Summary.init_function = (fun () ->
				       modtab_substobjs := MPmap.empty;
				       modtab_objects := MPmap.empty;
				       openmod_info := ((MPfile(initial_dir),
							 [],None,None));
				       library_cache := Dirmap.empty) }

(* auxiliary functions to transform full_path and kernel_name given
   by Lib into module_path and dir_path needed for modules *)

let mp_of_kn kn =
  let mp,sec,l = repr_kn kn in
    if sec=empty_dirpath then
      MPdot (mp,l)
    else
      anomaly ("Non-empty section in module name!" ^ string_of_kn kn)

let dir_of_sp sp =
  let dir,id = repr_path sp in
    add_dirpath_suffix dir id


(* This function checks if the type calculated for the module [mp] is
   a subtype of [sub_mtb]. Uses only the global environment. *)
let check_subtypes mp sub_mtb =
  let env = Global.env () in
  let mb = Environ.lookup_module mp env in
  let mtb = Modops.module_type_of_module env None mb in
  let _ = Environ.add_constraints 
    (Subtyping.check_subtypes env mtb sub_mtb) 
  in
    ()  (* The constraints are checked and forgot immediately! *)

(* These functions register the visibility of the module and iterates
   through its components. They are called by plenty module functions *)

let compute_visibility exists what i dir dirinfo =
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
(*
let do_load_and_subst_module i dir mp substobjs keep =
  let prefix = (dir,(mp,empty_dirpath)) in
  let dirinfo = DirModule (dir,(mp,empty_dirpath)) in
  let vis = compute_visibility false "load_and_subst" i dir dirinfo in
  let objects = compute_subst_objects mp substobjs resolver in
  Nametab.push_dir vis dir dirinfo;
  modtab_substobjs := MPmap.add mp substobjs !modtab_substobjs;
  match objects with
  | Some (subst,seg) ->
      let seg = load_and_subst_objects (i+1) prefix subst seg in
      modtab_objects := MPmap.add mp (prefix,seg) !modtab_objects;
      load_objects (i+1) prefix keep;
      Some (seg@keep)
  | None ->
      None
*)

let do_module exists what iter_objects i dir mp substobjs keep=
  let prefix = (dir,(mp,empty_dirpath)) in
  let dirinfo = DirModule (dir,(mp,empty_dirpath)) in
  let vis = compute_visibility exists what i dir dirinfo in
    Nametab.push_dir vis dir dirinfo;
    modtab_substobjs := MPmap.add mp substobjs !modtab_substobjs;
    match substobjs with
	([],mp1,objs) -> 
	  modtab_objects := MPmap.add mp (prefix,objs@keep) !modtab_objects;
	  iter_objects (i+1) prefix (objs@keep)  
      | (mbids,_,_) ->  ()

let conv_names_do_module exists what iter_objects i
      (sp,kn) substobjs =
  let dir,mp = dir_of_sp sp, mp_of_kn kn in
  do_module exists what iter_objects i dir mp substobjs []

(* Interactive modules and module types cannot be recached! cache_mod*
   functions can be called only once (and "end_mod*" set the flag to
   false then)
*)
let cache_module ((sp,kn),(entry,substobjs)) =
  let dir,mp = dir_of_sp sp, mp_of_kn kn in
    do_module false "cache" load_objects 1 dir mp substobjs []
    
(* TODO: This check is not essential *)
let check_empty s = function
     | None -> ()
     | Some _ ->
	 anomaly ("We should never have full info in " ^ s^"!")


(* When this function is called the module itself is already in the
   environment. This function loads its objects only *)

let load_module i (oname,(entry,substobjs)) =
  (* TODO: This check is not essential *)
  check_empty "load_module" entry;
  conv_names_do_module false "load" load_objects i oname substobjs


let open_module i (oname,(entry,substobjs)) =
  (* TODO: This check is not essential *)
  check_empty "open_module" entry;
  conv_names_do_module true "open" open_objects i oname substobjs



let subst_module (subst,(entry,(mbids,mp,objs))) =
  check_empty "subst_module" entry;
    (None,(mbids,subst_mp subst mp, subst_objects subst objs))


let classify_module (_,substobjs) =
  Substitute (None,substobjs)

let (in_module,out_module) =
  declare_object {(default_object "MODULE") with
    cache_function = cache_module;
    load_function = load_module;
    open_function = open_module;
    subst_function = subst_module;
    classify_function = classify_module }

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

let (in_modkeep,_) =
  declare_object {(default_object "MODULE KEEP OBJECTS") with
    cache_function = cache_keep;
    load_function = load_keep;
    open_function = open_keep }

(* we remember objects for a module type. In case of a declaration:
   Module M:SIG:=...
   The module M gets its objects from SIG
*)
let modtypetab =
  ref (MPmap.empty : substitutive_objects MPmap.t)

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
				       modtypetab := MPmap.empty;
				       openmodtype_info := []) }


let cache_modtype ((sp,kn),(entry,modtypeobjs)) =
  let _ =
    match entry with
      | None ->
	  anomaly "You must not recache interactive module types!"
      | Some mte ->
	  let mp = Global.add_modtype (basename sp) mte in
	  if mp <>mp_of_kn kn then
	    anomaly "Kernel and Library names do not match"
  in

  if Nametab.exists_modtype sp then
    errorlabstrm "cache_modtype"
      (pr_path sp ++ str " already exists") ;

  Nametab.push_modtype (Nametab.Until 1) sp (mp_of_kn kn);

  modtypetab := MPmap.add (mp_of_kn kn) modtypeobjs !modtypetab


let load_modtype i ((sp,kn),(entry,modtypeobjs)) =
  check_empty "load_modtype" entry;

  if Nametab.exists_modtype sp then
    errorlabstrm "cache_modtype"
      (pr_path sp ++ str " already exists") ;

  Nametab.push_modtype (Nametab.Until i) sp (mp_of_kn kn);

  modtypetab := MPmap.add (mp_of_kn kn) modtypeobjs !modtypetab


let open_modtype i ((sp,kn),(entry,_)) =
  check_empty "open_modtype" entry;

  if
    try Nametab.locate_modtype (qualid_of_path sp) <> (mp_of_kn kn)
    with Not_found -> true
  then
    errorlabstrm ("open_modtype")
      (pr_path sp ++ str " should already exist!");

  Nametab.push_modtype (Nametab.Exactly i) sp (mp_of_kn kn)

let subst_modtype (subst,(entry,(mbids,mp,objs))) =
  check_empty "subst_modtype" entry;
  (entry,(mbids,subst_mp subst mp,subst_objects subst objs))


let classify_modtype (_,substobjs) =
  Substitute (None,substobjs)


let (in_modtype,_) =
    declare_object {(default_object "MODULE TYPE") with
      cache_function = cache_modtype;
      open_function = open_modtype;
      load_function = load_modtype;
      subst_function = subst_modtype;
      classify_function = classify_modtype }


let rec replace_module_object idl ( mbids, mp, lib_stack) (mbids2,mp2,objs) mp1=
  if mbids<>[] then 
    error "Unexpected functor objects"
  else
    let rec replace_idl = function 
      | _,[] -> [] 
      | id::idl,(id',obj)::tail when id = id' ->
	  if object_tag obj = "MODULE" then
           (match idl with
               [] -> (id, in_module 
			(None,(mbids,(MPdot(mp,label_of_id id)),subst_objects 
				 (map_mp mp1 (MPdot(mp,label_of_id id)) empty_delta_resolver) objs)))::tail
             | _ ->
               let (_,substobjs) = out_module obj in
                let substobjs' = replace_module_object idl substobjs 
		  (mbids2,mp2,objs) mp in
                  (id, in_module (None,substobjs'))::tail
           )
	  else error "MODULE expected!"
      | idl,lobj::tail -> lobj::replace_idl (idl,tail)
    in
      (mbids, mp, replace_idl (idl,lib_stack))

let discr_resolver mb  = 
     match mb.mod_type with
	SEBstruct _ -> 
	  Some mb.mod_delta
      | _ -> (*case mp is a functor *)
	  None

(* Small function to avoid module typing during substobjs retrivial  *)
let rec get_objs_modtype_application env = function
| MSEident mp -> 
    MPmap.find mp !modtypetab,Environ.lookup_modtype mp env,[]
| MSEapply (fexpr, MSEident mp) -> 
    let objs,mtb,mp_l= get_objs_modtype_application env fexpr in
      objs,mtb,mp::mp_l
| MSEapply (_,mexpr) ->
    Modops.error_application_to_not_path mexpr
| _ -> error "Application of a non-functor."

let rec get_modtype_substobjs env mp_from= function
    MSEident ln -> 
      MPmap.find ln !modtypetab 
  | MSEfunctor (mbid,_,mte) ->
      let (mbids, mp, objs) = get_modtype_substobjs env mp_from mte in
	(mbid::mbids, mp, objs)
  | MSEwith (mty, With_Definition _) -> get_modtype_substobjs env mp_from mty
  | MSEwith (mty, With_Module (idl,mp1)) -> 
      let substobjs = get_modtype_substobjs env mp_from mty in
      let modobjs = MPmap.find mp1 !modtab_substobjs in
	replace_module_object idl substobjs modobjs mp1
  | MSEapply (fexpr, MSEident mp) ->
      let (mbids, mp1, objs),mtb_mp1,mp_l =  
	get_objs_modtype_application env (MSEapply(fexpr, MSEident mp)) in
      let rec compute_subst mbids sign mp_l =
	match mbids,mp_l with
	    [],[] -> [],empty_subst
	  | mbid,[] -> mbid,empty_subst
	  | [],r -> error ("Application of a functor with too few arguments.")
	  | mbid::mbids,mp::mp_l ->
	      let farg_id, farg_b, fbody_b = Modops.destr_functor env sign in
	      let mb = Environ.lookup_module mp env in
	      let mp_delta = discr_resolver mb in
	      let mbid_left,subst=compute_subst mbids fbody_b mp_l in
		if mp_delta = None then
		  mbid_left,join (map_mbid mbid mp empty_delta_resolver) subst 
		else
		  let mp_delta = Modops.complete_inline_delta_resolver env mp 
		    farg_id farg_b (Option.get mp_delta) in
		    mbid_left,join (map_mbid mbid mp mp_delta) subst
      in
      let mbids_left,subst = compute_subst mbids mtb_mp1.typ_expr (List.rev mp_l) in
	(mbids_left, mp1,subst_objects subst objs)
  | MSEapply (_,mexpr) ->
      Modops.error_application_to_not_path mexpr

(* push names of bound modules (and their components) to Nametab *)
(* add objects associated to them *)
let process_module_bindings argids args =
  let process_arg id (mbid,mty) =
    let dir = make_dirpath [id] in
    let mp = MPbound mbid in
    let (mbids,mp_from,objs) = get_modtype_substobjs (Global.env()) mp mty in
    let substobjs = (mbids,mp,subst_objects 
		       (map_mp mp_from mp empty_delta_resolver) objs)in
      do_module false "start" load_objects 1 dir mp substobjs []
    in
      List.iter2 process_arg argids args
	
let intern_args interp_modtype (idl,arg) =
  let lib_dir = Lib.library_dp() in
  let mbids = List.map (fun (_,id) -> make_mbid lib_dir (string_of_id id)) idl in
  let mty = interp_modtype (Global.env()) arg in
  let dirs = List.map (fun (_,id) -> make_dirpath [id]) idl in
  let (mbi,mp_from,objs) = get_modtype_substobjs (Global.env())
    (MPbound (List.hd mbids))  mty in
  List.map2
    (fun dir mbid ->
       let resolver = Global.add_module_parameter mbid mty in
       let mp = MPbound mbid in
       let substobjs = (mbi,mp,subst_objects 
			  (map_mp mp_from mp resolver) objs) in
	 do_module false "interp" load_objects 1 dir mp substobjs [];
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
	  if restricted then
	    let _ = Mod_typing.translate_struct_type_entry (Global.env()) mte in
	      Some mte, None
	  else
	    let mtb = Mod_typing.translate_module_type (Global.env())
	      mp mte in
	    let funct_mtb = 
	      List.fold_right 
		(fun (arg_id,arg_t) mte -> 
		let arg_t = Mod_typing.translate_module_type (Global.env())
		  (MPbound arg_id)  arg_t
		in
		  SEBfunctor(arg_id,arg_t,mte))
		arg_entries mtb.typ_expr
	    in
	      None, Some {mtb with 
			 typ_expr = funct_mtb}
  in

  let mbids = List.map fst arg_entries in
    openmod_info:=(mp,mbids,res_entry_o,sub_body_o);
  let prefix = Lib.start_module export id mp fs in
  Nametab.push_dir (Nametab.Until 1) (fst prefix) (DirOpenModule prefix);
  Lib.add_frozen_state (); mp


let end_module () =

  let oldoname,oldprefix,fs,lib_stack = Lib.end_module () in
  let mp,mbids, res_o, sub_o = !openmod_info in
  let substitute, keep, special = Lib.classify_segment lib_stack in

  let mp_from,substobjs, keep, special = try
    match res_o with
      | None ->
	  (* the module is not sealed *)
	  None,( mbids, mp, substitute), keep, special
      | Some (MSEident ln as mty) ->
	  let (mbids1,mp1,objs) = get_modtype_substobjs (Global.env()) mp mty in
	  Some mp1,(mbids@mbids1,mp1,objs), [], []
      | Some (MSEwith _ as mty) ->
	  let (mbids1,mp1,objs) = get_modtype_substobjs (Global.env()) mp mty in
	  Some mp1,(mbids@mbids1,mp1,objs), [], []
      | Some (MSEfunctor _) ->
	  anomaly "Funsig cannot be here..."
      | Some (MSEapply _ as mty) ->
	  let (mbids1,mp1,objs) = get_modtype_substobjs (Global.env()) mp mty in
	  Some mp1,(mbids@mbids1,mp1,objs), [], []
  with
	Not_found -> anomaly "Module objects not found..."
  in
    (* must be called after get_modtype_substobjs, because of possible
     dependencies on functor arguments *)

  let id = basename (fst oldoname) in
  let mp,resolver = Global.end_module fs id res_o in

  begin match sub_o with
      None -> ()
    | Some sub_mtb -> check_subtypes mp sub_mtb
  end;

(* we substitute objects if the module is 
   sealed by a signature (ie. mp_from != None *)
  let substobjs = match mp_from,substobjs with
      None,_ -> substobjs
    | Some mp_from,(mbids,_,objs) ->
	(mbids,mp,subst_objects (map_mp mp_from mp resolver) objs) 
  in
  let node = in_module (None,substobjs) in
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

    Lib.add_frozen_state () (* to prevent recaching *);
    mp



let module_objects mp =
  let prefix,objects = MPmap.find mp !modtab_objects in
    segment_of_objects prefix objects



(************************************************************************)
(* libraries *)

type library_name = dir_path

(* The first two will form substitutive_objects, the last one is keep *)
type library_objects =
    module_path * lib_objects * lib_objects


let register_library dir cenv objs digest =
  let mp = MPfile dir in
  let substobjs, keep =
  try 
    ignore(Global.lookup_module mp);
    (* if it's in the environment, the cached objects should be correct *)
    Dirmap.find dir !library_cache
  with Not_found ->
    if mp <> Global.import cenv digest then
      anomaly "Unexpected disk module name";
    let mp,substitute,keep = objs in
    let substobjs = [], mp, substitute in
    let modobjs = substobjs, keep in
    library_cache := Dirmap.add dir modobjs !library_cache;
      modobjs
  in
    do_module false "register_library" load_objects 1 dir mp substobjs keep

let start_library dir =
  let mp = Global.start_library dir in
  openmod_info:=mp,[],None,None;
  Lib.start_compilation dir mp;
  Lib.add_frozen_state ()

let end_library_hook = ref ignore
let set_end_library_hook f = end_library_hook := f

let end_library dir =
  !end_library_hook();
  let prefix, lib_stack = Lib.end_compilation dir in
  let mp,cenv = Global.export dir in
  let substitute, keep, _ = Lib.classify_segment lib_stack in
    cenv,(mp,substitute,keep)


(* implementation of Export M and Import M *)


let really_import_module mp =
  let prefix,objects = MPmap.find mp !modtab_objects in
    open_objects 1 prefix objects


let cache_import (_,(_,mp)) =
(* for non-substitutive exports:
  let mp = Nametab.locate_module (qualid_of_dirpath dir) in  *)
  really_import_module mp

let classify_import (export,_ as obj) =
  if export then Substitute obj else Dispose

let subst_import (subst,(export,mp as obj)) =
   let mp' = subst_mp subst mp in
    if mp'==mp then obj else
      (export,mp')

let (in_import,_) =
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
  Lib.add_frozen_state (); mp


let end_modtype () =
  let oldoname,prefix,fs,lib_stack = Lib.end_modtype () in
  let id = basename (fst oldoname) in
  let substitute, _, special = Lib.classify_segment lib_stack in
  let mbids = !openmodtype_info in
  let mp = Global.end_modtype fs id in
  let modtypeobjs = mbids, mp, substitute in  
  let oname = Lib.add_leaves id (special@[in_modtype (None, modtypeobjs)]) in

  if fst oname <> fst oldoname then
    anomaly
      "Section paths generated on start_ and end_modtype do not match";
  if (mp_of_kn (snd oname)) <> mp then
    anomaly
      "Kernel and Library names do not match";

  Lib.add_frozen_state ()(* to prevent recaching *);
  mp


let declare_modtype interp_modtype id args mty =
  let fs = Summary.freeze_summaries () in

  try
  let mmp = Global.start_modtype id in
  let arg_entries = List.concat (List.map (intern_args interp_modtype) args) in

  let base_mty = interp_modtype (Global.env()) mty in
  let entry =
    List.fold_right
      (fun (arg_id,arg_t) mte -> MSEfunctor(arg_id,arg_t,mte))
      arg_entries
      base_mty
  in
  let (mbids,mp_from,objs) = get_modtype_substobjs (Global.env()) mmp entry in
    (* Undo the simulated interactive building of the module type *)
    (* and declare the module type as a whole *)

  let substobjs = (mbids,mmp,
		   subst_objects (map_mp mp_from mmp empty_delta_resolver) objs) in
    Summary.unfreeze_summaries fs;
    ignore (add_leaf id (in_modtype (Some entry, substobjs)));
    mmp
  with e ->
    (* Something wrong: undo the whole process *)
    Summary.unfreeze_summaries fs; raise e

(* Small function to avoid module typing during substobjs retrivial  *)
let rec get_objs_module_application env = function
| MSEident mp -> 
    MPmap.find mp !modtab_substobjs,Environ.lookup_module mp env,[]
| MSEapply (fexpr, MSEident mp) -> 
    let objs,mtb,mp_l= get_objs_module_application env fexpr in
      objs,mtb,mp::mp_l
| MSEapply (_,mexpr) ->
    Modops.error_application_to_not_path mexpr
| _ -> error "Application of a non-functor."


let rec get_module_substobjs env mp_from = function
  | MSEident mp -> MPmap.find mp !modtab_substobjs
  | MSEfunctor (mbid,mty,mexpr) ->
       let (mbids, mp, objs) = get_module_substobjs env mp_from mexpr in
	(mbid::mbids, mp, objs)
  | MSEapply (fexpr, MSEident mp) ->
      let (mbids, mp1, objs),mb_mp1,mp_l =  
	get_objs_module_application env (MSEapply(fexpr, MSEident mp)) in
      let rec compute_subst mbids sign mp_l =
	match mbids,mp_l with
	    [],[] -> [],empty_subst
	  | mbid,[] -> mbid,empty_subst
	  | [],r -> error ("Application of a functor with too few arguments.")
	  | mbid::mbids,mp::mp_l ->
	      let farg_id, farg_b, fbody_b = Modops.destr_functor env sign in
	      let mb = Environ.lookup_module mp env in
	      let mp_delta = discr_resolver mb in
	      let mbid_left,subst=compute_subst mbids fbody_b mp_l in
		if mp_delta = None then
		  mbid_left,join (map_mbid mbid mp empty_delta_resolver) subst 
		else
		  let mp_delta = Modops.complete_inline_delta_resolver env mp 
		    farg_id farg_b (Option.get mp_delta) in
		    mbid_left,join (map_mbid mbid mp mp_delta) subst
      in
      let mbids_left,subst = compute_subst mbids mb_mp1.mod_type (List.rev mp_l) in
	(mbids_left, mp1,subst_objects subst objs)
    (*  let sign,alg,equiv,_ = Mod_typing.translate_struct_module_entry env mp_from fexpr in
      let farg_id, farg_b, fbody_b = Modops.destr_functor env sign in
      let mb = Environ.lookup_module mp env in
      let mp_delta = discr_resolver mb in
      let (mbids, mp1, objs) = get_module_substobjs env mp_from fexpr in
	(match mbids with
	   | mbid::mbids ->
	       if mp_delta = None then
		 (mbids, mp1,subst_objects (map_mbid mbid mp empty_delta_resolver) objs)
	       else
		 let mp_delta = Modops.complete_inline_delta_resolver env mp 
		   farg_id farg_b (Option.get mp_delta) in
		    (mbids, mp1,subst_objects (map_mbid mbid mp mp_delta) objs)
	   | [] -> match fexpr with
	       | MSEident _  -> error "Application of a non-functor."
	       | _ -> error "Application of a functor with too few arguments.")*)
  | MSEapply (_,mexpr) ->
      Modops.error_application_to_not_path mexpr
  | MSEwith (mty, With_Definition _) -> get_module_substobjs env mp_from mty
  | MSEwith (mty, With_Module (idl,mp)) -> assert false



(* Include *)

let rec subst_inc_expr subst me =
  match me with
    | MSEident mp -> MSEident (subst_mp subst mp)
    | MSEwith (me,With_Module(idl,mp)) ->
	MSEwith (subst_inc_expr subst me,
		 With_Module(idl,subst_mp subst mp))
    | MSEwith (me,With_Definition(idl,const))->
	let const1 = Mod_subst.from_val const in
	let force = Mod_subst.force subst_mps in
	MSEwith (subst_inc_expr subst me,
		 With_Definition(idl,force (subst_substituted
					   subst const1)))
    | MSEapply (me1,me2) ->
	MSEapply (subst_inc_expr subst me1,
		  subst_inc_expr subst me2)
    | _ -> anomaly "You cannot Include a high-order structure"

let lift_oname (sp,kn) =
  let mp,_,_ = Names.repr_kn kn in
  let dir,_ = Libnames.repr_path sp in
    (dir,mp)

let cache_include (oname,((me,is_mod),(mbis,mp1,objs))) =
  let dir,mp1 = lift_oname oname in
  let prefix = (dir,(mp1,empty_dirpath)) in
    load_objects 1 prefix objs;
    open_objects 1 prefix objs 
    
let load_include  i (oname,((me,is_mod),(mbis,mp1,objs))) =
  let dir,mp1 = lift_oname oname in
  let prefix = (dir,(mp1,empty_dirpath)) in
    load_objects i prefix objs
      
      
let open_include i (oname,((me,is_mod),(mbis,mp1,objs))) =
  let dir,mp1 = lift_oname oname in
  let prefix = (dir,(mp1,empty_dirpath)) in
      if is_mod || i = 1 then
	open_objects i prefix objs
      else ()
    
let subst_include (subst,((me,is_mod),substobj)) =
  let (mbids,mp,objs) = substobj in
  let substobjs = (mbids,subst_mp subst mp,subst_objects subst objs) in
    ((subst_inc_expr subst me,is_mod),substobjs)
      
let classify_include ((me,is_mod),substobjs) =
  Substitute ((me,is_mod),substobjs)

let (in_include,out_include) =
  declare_object {(default_object "INCLUDE") with
    cache_function = cache_include;
    load_function = load_include;
    open_function = open_include;
    subst_function = subst_include;
    classify_function = classify_include }

let rec update_include (mbids,mp,objs) =
  let rec replace_include = function
    | [] -> []
    | (id,obj)::tail ->
	if object_tag obj = "INCLUDE" then
	  let ((me,is_mod),substobjs) = out_include obj in
	  let substobjs' = update_include substobjs in
            (id, in_include ((me,true),substobjs'))::
	      (replace_include tail)
	else
	  (id,obj)::(replace_include tail)
  in
    (mbids,mp,replace_include objs)

let declare_module interp_modtype interp_modexpr id args mty_o mexpr_o =

  let fs = Summary.freeze_summaries () in

  try
  let mmp = Global.start_module id in
  let arg_entries = List.concat (List.map (intern_args interp_modtype) args) in

  let mty_entry_o, mty_sub_o = match mty_o with
      None -> None, None
    | (Some (mty, true)) ->
	Some (List.fold_right
		(fun (arg_id,arg_t) mte -> MSEfunctor(arg_id,arg_t,mte))
		arg_entries
		(interp_modtype (Global.env()) mty)),
	None
    | (Some (mty, false)) ->
	None,
	Some (List.fold_right
		(fun (arg_id,arg_t) mte -> MSEfunctor(arg_id,arg_t,mte))
		arg_entries
		(interp_modtype (Global.env()) mty))
  in
  let mexpr_entry_o = match mexpr_o with
      None -> None
    | Some mexpr ->
	Some (List.fold_right
		(fun (mbid,mte) me -> MSEfunctor(mbid,mte,me))
		arg_entries
		(interp_modexpr (Global.env()) mexpr))  in
  let entry =
    {mod_entry_type = mty_entry_o;
     mod_entry_expr = mexpr_entry_o }
  in
  let env = Global.env() in
  let substobjs =
    match entry with
      | {mod_entry_type = Some mte} -> get_modtype_substobjs env mmp mte
      | {mod_entry_expr = Some mexpr} -> get_module_substobjs env mmp mexpr
      | _ -> anomaly "declare_module: No type, no body ..."
  in
  let (mbids,mp_from,objs) = update_include substobjs in
    (* Undo the simulated interactive building of the module *)
    (* and declare the module as a whole *)
    Summary.unfreeze_summaries fs;
    let dir,mp = dir_of_sp (Lib.make_path id), mp_of_kn (Lib.make_kn id) in
    let mp_env,resolver = Global.add_module id entry in
    let _ = if mp_env <> mp then
      anomaly "Kernel and Library names do not match";
      match  mty_sub_o with
	| None -> ()
	| Some sub_mte -> 
	    let sub_mtb = Mod_typing.translate_module_type
	      env mp sub_mte in
	      check_subtypes mp_env sub_mtb
    in
    let substobjs = (mbids,mp_env,
		     subst_objects(map_mp mp_from mp_env resolver) objs) in
      ignore (add_leaf
		id
		(in_module (Some (entry, mty_sub_o), substobjs)));
      mmp
	
  with e -> 
    (* Something wrong: undo the whole process *)
    Summary.unfreeze_summaries fs; raise e


let declare_include interp_struct me_ast is_mod =

  let fs = Summary.freeze_summaries () in

    try
      let env = Global.env() in
      let me = interp_struct env me_ast in 
      let mp1,_ = current_prefix () in
      let (mbids,mp,objs)= 	
	if is_mod then
	  get_module_substobjs env mp1 me
	else
	  get_modtype_substobjs env mp1 me in
      let id = current_mod_id() in
      let resolver =  Global.add_include me is_mod in
      let substobjs = (mbids,mp1,
		       subst_objects (map_mp mp mp1 resolver) objs) in
	ignore (add_leaf id
		  (in_include ((me,is_mod), substobjs)))
    with e ->
      (* Something wrong: undo the whole process *)
      Summary.unfreeze_summaries fs; raise e


(*s Iterators. *)

let iter_all_segments f =
  let _ =
    MPmap.iter
      (fun _ (prefix,objects) ->
	 let rec apply_obj (id,obj) = match object_tag obj with 
	   | "INCLUDE" -> 
	       let (_,(_,_,objs)) =  out_include obj in 
		 List.iter apply_obj objs
		   
	   | _ -> f (make_oname prefix id) obj in
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
