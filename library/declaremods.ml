(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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

(* modules and components *)


(* This type is a functional closure of a substitutive
   library_segment.

   The first part is a partial substitution (which will be later
   applied to the library_segment when completed).

   The second one is a list of bound identifiers which is nonempty
   only if the segment is owned by a fuctor

   The third one is the "magic" ident of the current structure (which
   should be substituted with the real name of the current module.

   The fourth one is the segment itself which can contain references
   to identifiers in the domain of the substitution or in other two
   elements. These references are invalid in the current scope and
   therefore must be substitued with valid names before use.

*)

type substitutive_objects = 
    substitution * mod_bound_id list * mod_self_id * library_segment


(* For each module, we store the following things:

   substitutive_objects 
     when we will do Module M:=N, the objects of N will be loaded 
     with M as well (after substitution)

   substituted objects - 
     roughly the objects above after the substitution - we need to 
     keep them to call open_object when the module is opened (imported)
 
   keep objects -
     The list of non-substitutive objects - as above, for each of 
     them we will call open_object when the module is opened 
     
   (Some) Invariants:
   * If the module is a functor, the two latter lists are empty.

   * Module objects in substitutive_objects part have empty substituted 
     objects and keep objects.

   * Modules which where created with Module M:=mexpr (and not with 
     End Module) have the keep list empty.
*)


type module_objects = 
    substitutive_objects * library_segment * library_segment

let modtab = ref (MPmap.empty  :  module_objects MPmap.t)
    
(* currently begun interactive module (if any) - its arguments (if it
   is a functor) and declared output type *)
let openmod_info = 
  ref (([],None) : mod_bound_id list * module_type_entry option) 

let _ = Summary.declare_summary "MODULE-INFO"
	  { Summary.freeze_function = (fun () -> !modtab,!openmod_info);
	    Summary.unfreeze_function = (fun ft -> 
					   modtab := fst ft; 
					   openmod_info := snd ft);
	    Summary.init_function = (fun () -> 
				       modtab := MPmap.empty; 
				       openmod_info := ([],None));
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

(* This function registers the visibility of the module and iterates
   through its components. It is called by plenty module functions *)

let do_module exists what iter_segment i dir mp modobjs =
  let (_,substituted,keep) = modobjs in
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
    modtab := MPmap.add mp modobjs !modtab;
    iter_segment (i+1) substituted;
    iter_segment (i+1) keep
    
let conv_names_do_module exists what iter_segment i (sp,kn) decl =
  let dir,mp = dir_of_sp sp, mp_of_kn kn in
  do_module exists what iter_segment i dir mp decl

(* Interactive modules and module types cannot be recached! cache_mod*
   functions can be called only once (and "end_mod*" set the flag to
   false then)
*)

let recache_protection = ref true

let cache_module ((sp,kn as oname),(entry,decl)) =
  let _ = match entry with
    | None ->
	if !recache_protection then
	  anomaly "You must not recache interactive modules!"
	else
	  recache_protection := true
    | Some me ->
	let mp = Global.add_module (basename sp) me in
	if mp <> mp_of_kn kn then
	  anomaly "Kernel and Library names do not match"
  in
    conv_names_do_module false "cache" load_segment 1 oname decl


(* TODO: This check is not essential *)
let check_empty s = function
     | None -> ()
     | Some _ -> 
	 anomaly ("We should never have full info in " ^ s^"!")


(* When this function is called the module itself is already in the
   environment. This function loads its objects only *)

let load_module i (oname,(entry,decl)) =
  (* TODO: This check is not essential *)
  check_empty "load_module" entry;
  conv_names_do_module false "load" load_segment i oname decl


let open_module i (oname,(entry,decl)) =
  (* TODO: This check is not essential *)
  check_empty "open_module" entry;
  conv_names_do_module true "open" open_segment i oname decl


let subst_substobjs dir mp (subst,mbids,msid,objs) =
  match mbids with
    | [] -> 
	let prefix = dir,(mp,empty_dirpath) in
	  subst_segment prefix (add_msid msid mp subst) objs
    | _ -> []


let subst_module ((sp,kn),subst,(entry,(substobjs,_,keep))) =
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
    (None,(substobjs,substituted,keep))


let classify_module (_,(_,(substobjs,_,keep))) =
  Substitute (None,(substobjs,[],keep))

let (in_module,out_module) =
  declare_object {(default_object "MODULE") with
    cache_function = cache_module;
    load_function = load_module;
    open_function = open_module;
    subst_function = subst_module;
    classify_function = classify_module;
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
	    Summary.survive_section = true }




let cache_modtype ((sp,kn),(entry,modtypeobjs)) =
  let _ = 
    match entry with
      | None ->
	  if !recache_protection then
	    warning "You must not recache interactive module types!"
	  else
	    recache_protection := true
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
      load_function = load_modtype;
      subst_function = subst_modtype;
      classify_function = classify_modtype;
      export_function = in_some }



let abstract_substobjs mbids1 (subst, mbids2, msid, lib_stack) =
  (subst, mbids1@mbids2, msid, lib_stack)


let rec get_modtype_substobjs = function
    MTEident ln -> KNmap.find ln !modtypetab
  | MTEfunsig (mbid,_,mte) ->
      let (subst, mbids, msid, objs) = get_modtype_substobjs mte in
	(subst, mbid::mbids, msid, objs)
  | MTEsig (msid,_) -> (empty_subst, [], msid, [])
        (* this is plainly wrong, but it is hard to do otherwise... *)

(* push names of bound modules (and their components) to Nametab *)
(* add objects associated to them *)
let process_module_bindings argids args =
  let process_arg id (mbid,mty) =
    let dir = make_dirpath [id] in
    let mp = MPbound mbid in
    let substobjs = get_modtype_substobjs mty in
    let substituted = subst_substobjs dir mp substobjs in
    let modobjs = substobjs, substituted, [] in
      do_module false "begin" load_segment 1 dir mp modobjs
  in
    List.iter2 process_arg argids args


(* this function removes keep objects from submodules *) 
let rec kill_keep objs =
  let kill = function
    | (oname,Leaf obj) as node ->
	if object_tag obj = "MODULE" then
	  let (entry,(substobjs,substitute,keep)) = out_module obj in
	    match substitute,keep with
	      | [],[] -> node
	      | _ -> oname, Leaf (in_module (entry,(substobjs,[],[])))
	else
	  node
    | _ -> anomaly "kill_keep expects Leafs only!"
  in
    match objs with
      | [] -> objs
      | h::tl -> let h'=kill h and tl'=kill_keep tl in
	  if h==h' && tl==tl' then
	    objs
	  else
	    h'::tl'


let start_module id argids args res_o =
  let mp = Global.start_module (Lib.module_dp()) id args res_o in
  let mbids = List.map fst args in
  let fs = Summary.freeze_summaries () in
    process_module_bindings argids args;
    openmod_info:=(mbids,res_o);
    Lib.start_module id mp fs;
    Lib.add_frozen_state ()


let end_module id =

  let oldoname,oldprefix,fs,lib_stack = Lib.end_module id in
  let mp = Global.end_module id in
  let substitute, keep, special = Lib.classify_segment lib_stack in
  Summary.unfreeze_other_summaries fs;

  let dir = fst oldprefix in
  let msid = msid_of_prefix oldprefix in
  let mbids, res_o = !openmod_info in
  let modobjs = match res_o with
      None ->
	(* we kill_keeps in submodules to store them in substobjs,
	   but leave them in substituted ! *)
	let substitute' = kill_keep substitute in
	let substobjs = (empty_subst, mbids, msid, substitute') in
	  (match mbids with
	    | [] ->
		let newprefix = dir,(mp,empty_dirpath) in
		let substituted =
		  subst_segment newprefix (map_msid msid mp) substitute 
		                                             (* no ' *)
		in
		let keep = change_kns mp keep  in
		  substobjs, substituted, keep
	    | _ ->
		substobjs,[],[])

    | Some (MTEident ln) ->
	let substobjs =
	  abstract_substobjs mbids (KNmap.find ln (!modtypetab))
	in
	  substobjs, subst_substobjs dir mp substobjs, []
		
    | Some (MTEsig (msid,_)) ->
	(empty_subst, mbids, msid, []), [], []

    | Some (MTEfunsig _) -> anomaly "Funsig cannot be here..."

  in

    recache_protection := false;
    let newoname = Lib.add_leaves special id (in_module (None,modobjs)) in

    if (fst newoname) <> (fst oldoname) then
      anomaly "Names generated on start_ and end_module do not match";
    if mp_of_kn (snd newoname) <> mp then 
      anomaly "Kernel and Library names do not match";

    Lib.add_frozen_state () (* to prevent recaching *)






type library_name = dir_path

(* The first two will form a substitutive_objects, the last one is keep *)
type library_objects = 
    Names.mod_self_id * Lib.library_segment * Lib.library_segment


(* The library_cache here is needed to avoid recalculations of
   substituted modules object during "reloading" of libraries *)
let library_cache = Hashtbl.create 17


let register_library dir cenv objs digest =
  let mp = MPfile dir in
  let modobjs = 
    try 
      ignore(Global.lookup_module mp);
      (* if it's in the environment, the cached objects should be correct *)
      Hashtbl.find library_cache dir
    with
	Not_found ->
	  if mp <> Global.import cenv digest then
	    anomaly "Unexpected disk module name";
	  let msid,substitute,keep = objs in
	  let substitute' = kill_keep substitute in
	  let substobjs = (empty_subst, [], msid, substitute') in
	  let prefix = dir, (mp, empty_dirpath) in
	  let substituted =
	    subst_segment prefix (map_msid msid mp) substitute (* no ' *)
	  in
	  let modobjs = substobjs, substituted, keep in
	    Hashtbl.add library_cache dir modobjs;
	    modobjs
  in
    do_module false "register_compilation" load_segment 1 dir mp modobjs

let start_library dir = 
  let mp = Global.start_library dir in
  openmod_info:=[],None;
  Lib.start_compilation dir mp;
  Lib.add_frozen_state ()


let export_library dir = 
  let cenv = Global.export dir in
  let prefix, lib_stack = Lib.end_compilation dir in
  let msid = msid_of_prefix prefix in
  let substitute, keep, _ = Lib.classify_segment lib_stack in
  let keep = change_kns (MPfile dir) keep in
    cenv,(msid,substitute,keep)



let import_module mp =
  let (_,substituted,keep) = MPmap.find mp !modtab in
    open_segment 1 substituted;
    open_segment 1 keep



let start_modtype id argids args =
  let mp = Global.start_modtype (Lib.module_dp()) id args in
  let fs= Summary.freeze_summaries () in
    process_module_bindings argids args;
    openmodtype_info := (List.map fst args);
    Lib.start_modtype id mp fs;
    Lib.add_frozen_state ()


let end_modtype id =

  let oldoname,prefix,fs,lib_stack = Lib.end_modtype id in
  let ln = Global.end_modtype id in
  let substitute, _, special = Lib.classify_segment lib_stack in
  Summary.unfreeze_other_summaries fs;

  let msid = msid_of_prefix prefix in
  let mbids = !openmodtype_info in
  let modtypeobjs = empty_subst, mbids, msid, lib_stack in

  recache_protection := false;
  let oname = Lib.add_leaves special id (in_modtype (None, modtypeobjs)) in
  if fst oname <> fst oldoname then
    anomaly
      "Section paths generated on start_ and end_modtype do not match";
  if snd oname <> ln then
    anomaly
      "Kernel and Library names do not match";

  Lib.add_frozen_state ()(* to prevent recaching *)


let declare_modtype id mte = 
  let substobjs = get_modtype_substobjs mte in
    ignore (add_leaf id (in_modtype (Some mte, substobjs)))
			       


let rec get_module_substobjs = function
    MEident mp -> let (substobjs,_,_) = MPmap.find mp !modtab in substobjs
  | MEfunctor (mbid,_,mexpr) ->
      let (subst, mbids, msid, objs) = get_module_substobjs mexpr in
	(subst, mbid::mbids, msid, objs)
  | MEstruct (msid,_) ->
      (empty_subst, [], msid, [])
  | MEapply (mexpr, MEident mp) ->
      let (subst, mbids, msid, objs) = get_module_substobjs mexpr in
	(match mbids with
	   | mbid::mbids ->
	       (add_mbid mbid mp subst, mbids, msid, objs)
	   | [] -> anomaly "Too few arguments in functor")
  | MEapply (_,_) ->
      anomaly "The argument of a module application must be a path!"


let declare_module id me =
  let substobjs =
    match me with
      | {mod_entry_type = Some mte} -> get_modtype_substobjs mte
      | {mod_entry_expr = Some mexpr} -> get_module_substobjs mexpr
      | _ -> anomaly "declare_module: No type, no body ..."
  in
  let dir,mp = dir_of_sp (Lib.make_path id), mp_of_kn (Lib.make_kn id) in
  let substituted = subst_substobjs dir mp substobjs in
    ignore (add_leaf
	      id
	      (in_module (Some me, (substobjs, substituted, []))))


(*s Iterators. *)

let fold_all_segments insec f x =
  let rec apply acc = function
    | sp, Leaf o -> f acc sp o
    | _, ClosedSection (_,_,seg) -> 
	if insec then List.fold_left apply acc seg else acc
    | _ -> acc
  in
  let acc' = 
    MPmap.fold 
      (fun _ (_,substituted,keep) acc -> 
	 let acc' = List.fold_left apply acc substituted in
	   List.fold_left apply acc' keep)
      !modtab x
  in
    List.fold_left apply acc' (Lib.contents_after None)

let iter_all_segments insec f =
  let rec apply = function
    | sp, Leaf o -> f sp o
    | _, ClosedSection (_,_,seg) -> if insec then List.iter apply seg
    | _ -> ()
  in
    MPmap.iter 
      (fun _ (_,substituted,keep) -> 
	 List.iter apply substituted;
	 List.iter apply keep) 
      !modtab;
    List.iter apply (Lib.contents_after None)



let debug_print_modtab _ =
  let pr_seg = function
    | [] -> str "[]"
    | l -> str ("[." ^ string_of_int (List.length l) ^ ".]")
  in
  let pr_modinfo mp (_,substituted,keep) s =
    s ++ str (string_of_mp mp) ++ (spc ())
    ++ (pr_seg substituted) ++ (spc ())
    ++ pr_seg keep ++ (fnl ())
  in
  let modules = MPmap.fold pr_modinfo !modtab (mt ()) in
    hov 0 modules


