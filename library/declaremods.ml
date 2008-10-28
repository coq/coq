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
  ref (([],None,None) : mod_bound_id list * module_struct_entry option 
                                          * struct_expr_body option) 

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
				       openmod_info := ([],None,None);
				       library_cache := Dirmap.empty);
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

let is_bound mp =
  match mp with
    | MPbound _ -> true
    | _ -> false

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

let scrape_alias mp =
  Environ.scrape_alias mp (Global.env())
	

(* This function checks if the type calculated for the module [mp] is
   a subtype of [sub_mtb]. Uses only the global environment. *)
let check_subtypes mp sub_mtb =
  let env = Global.env () in
  let mtb = Environ.lookup_modtype mp env in
  let sub_mtb = 
    {typ_expr = sub_mtb;
    typ_strength = None;
    typ_alias = empty_subst} in
  let _ = Environ.add_constraints 
	    (Subtyping.check_subtypes env mtb sub_mtb) 
  in
    ()  (* The constraints are checked and forgot immediately! *) 

let subst_substobjs dir mp (subst,mbids,msid,objs) =
  match mbids with
    | [] -> 
	let prefix = dir,(mp,empty_dirpath) in
	let subst' = join_alias (map_msid msid mp) subst in
	let subst = join subst' subst in
	  Some (subst_objects prefix (join (map_msid msid mp) subst) objs)
    | _ -> None

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
	  | Some mte -> Some (Mod_typing.translate_struct_entry
				(Global.env()) mte)
	in
	  
	let mp = Global.add_module (basename sp) me in
	  if mp <> mp_of_kn kn then
	    anomaly "Kernel and Library names do not match";
	  
	  match sub_mtb_o with
	      None -> ()
	    | Some (sub_mtb,sub) -> 
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



let subst_module ((sp,kn),subst,(entry,substobjs,_)) =
  check_empty "subst_module" entry;
  let dir,mp = dir_of_sp sp, mp_of_kn kn in
  let (sub,mbids,msid,objs) = substobjs in
  let sub = subst_key subst sub in
  let sub' = update_subst_alias subst sub in
  let sub' = update_subst_alias sub' (map_msid msid mp) in
 (* let sub = join_alias sub sub' in*)
  let sub = join sub' sub in
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


let rec replace_alias modalias_obj obj =
  let rec put_alias (id_alias,obj_alias) l =
    match l with 
	[] -> []
      | (id,o)::r 
	  when ( object_tag o = "MODULE") ->
	  if id = id_alias then
(*	    let (entry,subst_o,substed_o) = out_module_alias obj_alias in
	    let (entry',subst_o',substed_o') = out_module o in
	      begin
		match substed_o,substed_o' with
		    Some a,Some b ->
		      (id,in_module_alias 
			 (entry,subst_o',Some (dump_alias_object a b)))::r*)
	    (id_alias,obj_alias)::r
		 (* | _,_ -> (id,o)::r
	      end*)
	  else (id,o)::(put_alias (id_alias,obj_alias) r)
      | e::r -> e::(put_alias (id_alias,obj_alias) r) in
  let rec choose_obj_alias list_alias list_obj =
    match list_alias with
      | [] -> list_obj
      | o::r ->choose_obj_alias r (put_alias o list_obj) in
    choose_obj_alias modalias_obj obj
	  
and dump_alias_object alias_obj obj =
  let rec alias_in_obj seg =
    match seg with
      | [] -> []
      | (id,o)::r when (object_tag o = "MODULE ALIAS") -> 
	  (id,o)::(alias_in_obj r)
      | e::r -> (alias_in_obj r) in
  let modalias_obj = alias_in_obj alias_obj in
    replace_alias modalias_obj obj
      
and do_module_alias exists what iter_objects i dir mp alias substobjs objects =
  let prefix = (dir,(alias,empty_dirpath)) in
  let alias_objects = 
    try Some (MPmap.find alias !modtab_objects) with
	Not_found -> None in
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
    match alias_objects,objects with
	Some (_,seg), Some seg' -> 
	  let new_seg = dump_alias_object seg seg' in
	  modtab_objects := MPmap.add mp (prefix,new_seg) !modtab_objects;
	  iter_objects (i+1) prefix new_seg 	  
      | _,_->  ()

and cache_module_alias ((sp,kn),(entry,substobjs,substituted)) =
  let dir,mp,alias = match entry with
    | None ->
	anomaly "You must not recache interactive modules!"
    | Some (me,sub_mte_o) ->
	let sub_mtb_o = match sub_mte_o with 
	    None -> None
	  | Some mte -> Some (Mod_typing.translate_struct_entry
				(Global.env()) mte)
	in

	let mp' = match me with 
	  | {mod_entry_type = None;
	     mod_entry_expr = Some (MSEident mp)} ->
	      Global.add_alias (basename sp) mp	 
	  | _ -> anomaly "cache module alias"
	in
	  if mp' <> mp_of_kn kn then
	    anomaly "Kernel and Library names do not match";
	  
	  let _ = match sub_mtb_o with
	      None -> ()
	    | Some (sub_mtb,sub) -> 
	      check_subtypes mp' sub_mtb in
	    match me with
	      | {mod_entry_type = None;
		 mod_entry_expr = Some (MSEident mp)} ->
		    dir_of_sp sp,mp_of_kn kn,scrape_alias mp		
	      | _ -> anomaly "cache module alias"
  in
    do_module_alias false "cache" load_objects 1 dir mp alias substobjs substituted

and load_module_alias i ((sp,kn),(entry,substobjs,substituted)) =
  let dir,mp,alias= 
    match entry with 
      | Some (me,_)->
	  begin
	    match me with
	      |{mod_entry_type = None;
		mod_entry_expr = Some (MSEident mp)} ->
		 dir_of_sp sp,mp_of_kn kn,scrape_alias mp
	      | _ -> anomaly "Modops: Not an alias"
	  end
      | None -> anomaly "Modops: Empty info"
  in
    do_module_alias false "load" load_objects i dir mp alias substobjs substituted

and open_module_alias i ((sp,kn),(entry,substobjs,substituted)) =
  let dir,mp,alias=
    match entry with 
      | Some (me,_)->
	  begin
	    match me with
	      |{mod_entry_type = None;
		mod_entry_expr = Some (MSEident mp)} ->
		 dir_of_sp sp,mp_of_kn kn,scrape_alias mp
	      | _ -> anomaly "Modops: Not an alias"
	  end
      | None -> anomaly "Modops: Empty info"
  in
    do_module_alias true "open" open_objects i dir mp alias substobjs substituted

and subst_module_alias ((sp,kn),subst,(entry,substobjs,_)) =
  let dir,mp = dir_of_sp sp, mp_of_kn kn in
  let (sub,mbids,msid,objs) = substobjs in
  let sub' = update_subst_alias subst (map_msid msid mp) in
  let subst' = join sub' subst in
  let subst' = join sub subst' in
  (* substitutive_objects get the new substitution *)
  let substobjs = (subst',mbids,msid,objs) in
  (* if we are not a functor - calculate substitued.
     We add "msid |-> mp" to the substitution *)
    match entry with 
      | Some (me,sub)->
	  begin
	    match me with
	      |{mod_entry_type = None;
		mod_entry_expr = Some (MSEident mp')} ->
		 let mp' = subst_mp subst' mp' in
		 let mp' = scrape_alias mp' in
		   (Some ({mod_entry_type = None;
			 mod_entry_expr = 
			      Some (MSEident mp')},sub),
		    substobjs, match mbids with
		      | [] -> let subst = update_subst subst' (map_mp mp' mp) in
			  Some (subst_objects (dir,(mp',empty_dirpath)) 
				  (join (join subst' subst) (join (map_msid msid mp')
						  (map_mp mp mp')))
				   objs)
			    
		      | _ -> None)
		     
	      | _ -> anomaly "Modops: Not an alias"
	  end
      | None -> anomaly "Modops: Empty info"

and classify_module_alias (_,(entry,substobjs,_)) =
  Substitute (entry,substobjs,None)
	        
let (in_module_alias,out_module_alias) =
  declare_object {(default_object "MODULE ALIAS") with
		    cache_function = cache_module_alias;
		    open_function = open_module_alias;
		    classify_function = classify_module_alias;
		    subst_function = subst_module_alias;
		    load_function = load_module_alias;  
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
				       openmodtype_info := []);
	    Summary.survive_module = false;
	    Summary.survive_section = true }


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
      (pr_sp sp ++ str " already exists") ;

  Nametab.push_modtype (Nametab.Until 1) sp (mp_of_kn kn);

  modtypetab := MPmap.add (mp_of_kn kn) modtypeobjs !modtypetab


let load_modtype i ((sp,kn),(entry,modtypeobjs)) =
  check_empty "load_modtype" entry;

  if Nametab.exists_modtype sp then
    errorlabstrm "cache_modtype"
      (pr_sp sp ++ str " already exists") ;

  Nametab.push_modtype (Nametab.Until i) sp (mp_of_kn kn);
    
  modtypetab := MPmap.add (mp_of_kn kn) modtypeobjs !modtypetab


let open_modtype i ((sp,kn),(entry,_)) =
  check_empty "open_modtype" entry;

  if 
    try Nametab.locate_modtype (qualid_of_sp sp) <> (mp_of_kn kn) 
    with Not_found -> true
  then
    errorlabstrm ("open_modtype") 
      (pr_sp sp ++ str " should already exist!");

  Nametab.push_modtype (Nametab.Exactly i) sp (mp_of_kn kn)

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



let rec replace_module_object idl (subst, mbids, msid, lib_stack) modobjs mp =
  let rec mp_rec = function
    | [] -> MPself msid
	| i::r -> MPdot(mp_rec r,label_of_id i)
  in 
    if mbids<>[] then 
    error "Unexpected functor objects"
    else
      let rec replace_idl = function 
	| _,[] -> [] 
	| id::idl,(id',obj)::tail when id = id' ->
	    let tag = object_tag obj in
	    if tag = "MODULE" or tag ="MODULE ALIAS" then
              (match idl with
		   [] -> (id, in_module_alias (Some
						 ({mod_entry_type = None;
						   mod_entry_expr = Some (MSEident mp)},None)
						 ,modobjs,None))::tail
		 | _ ->
		     let (a,substobjs,_) = if tag =  "MODULE ALIAS" then
		       out_module_alias obj else out_module obj in
                     let substobjs' = replace_module_object idl substobjs modobjs mp in
  		       if tag =  "MODULE ALIAS" then
			 (id, in_module_alias (a,substobjs',None))::tail
		       else
			 (id, in_module (None,substobjs',None))::tail
              )
	    else error "MODULE expected!"
	| idl,lobj::tail -> lobj::replace_idl (idl,tail)
      in
	(join (map_mp (mp_rec (List.rev idl)) mp) subst, mbids, msid, replace_idl (idl,lib_stack))
	  
let abstract_substobjs mbids1 (subst, mbids2, msid, lib_stack) =
  (subst, mbids1@mbids2, msid, lib_stack)

let rec get_modtype_substobjs env = function
    MSEident ln -> MPmap.find ln !modtypetab
  | MSEfunctor (mbid,_,mte) ->
      let (subst, mbids, msid, objs) = get_modtype_substobjs env mte in
	(subst, mbid::mbids, msid, objs)
  | MSEwith (mty, With_Definition _) -> get_modtype_substobjs env mty
  | MSEwith (mty, With_Module (idl,mp)) -> 
      let substobjs = get_modtype_substobjs env mty in
      let modobjs = MPmap.find mp !modtab_substobjs in
	replace_module_object idl substobjs modobjs mp
  | MSEapply (mexpr, MSEident mp) ->
     let ftb,sub1 = Mod_typing.translate_struct_entry env mexpr in
      let farg_id, farg_b, fbody_b = Modops.destr_functor env 
	(Modops.eval_struct env ftb) in
      let mp = Environ.scrape_alias mp env in
      let sub_alias = (Environ.lookup_modtype mp env).typ_alias in
      let sub_alias = match Modops.eval_struct env (SEBident mp) with
	| SEBstruct (msid,sign) -> join_alias 
	    (subst_key (map_msid msid mp) sub_alias)
	      (map_msid msid mp)
	| _ -> sub_alias in
    let sub3=
	if sub1 = empty_subst then
	  update_subst sub_alias (map_mbid farg_id mp None)
	else
	  let sub1' = join_alias sub1 (map_mbid farg_id mp None) in
	  let sub_alias' =  update_subst sub_alias sub1' in
	    join sub1' sub_alias'
      in
      let sub3 = join sub3 (update_subst sub_alias (map_mbid farg_id mp None)) in
       let (subst, mbids, msid, objs) = get_modtype_substobjs env mexpr in
	(match mbids with
	   | mbid::mbids ->
               let resolve =
		 Modops.resolver_of_environment farg_id farg_b mp sub_alias env in
		 (* application outside the kernel, only for substitutive
                    objects (that are all non-logical objects) *)
		((join 
		    (join subst (map_mbid mbid mp (Some resolve)))
		       sub3)
		       , mbids, msid, objs)
	   | [] -> match mexpr with
	       | MSEident _  -> error "Application of a non-functor"
	       | _ -> error "Application of a functor with too few arguments")
  | MSEapply (_,mexpr) ->
      Modops.error_application_to_not_path mexpr

 
(* push names of bound modules (and their components) to Nametab *)
(* add objects associated to them *)
let process_module_bindings argids args =
  let process_arg id (mbid,mty) =
    let dir = make_dirpath [id] in
    let mp = MPbound mbid in
    let substobjs = get_modtype_substobjs (Global.env()) mty in
    let substituted = subst_substobjs dir mp substobjs in
      do_module false "start" load_objects 1 dir mp substobjs substituted
  in
    List.iter2 process_arg argids args

let intern_args interp_modtype (idl,arg) = 
  let lib_dir = Lib.library_dp() in
  let mbids = List.map (fun (_,id) -> make_mbid lib_dir (string_of_id id)) idl in
  let mty = interp_modtype (Global.env()) arg in
  let dirs = List.map (fun (_,id) -> make_dirpath [id]) idl in
  let substobjs = get_modtype_substobjs (Global.env()) mty in
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
	if restricted then
	  Some mte, None
	else
	  let mtb,_ = Mod_typing.translate_struct_entry (Global.env()) mte in
	  let sub_mtb = 
	    List.fold_right 
	      (fun (arg_id,arg_t) mte -> 
		let arg_t,sub = Mod_typing.translate_struct_entry (Global.env()) arg_t
		in
		let arg_t = {typ_expr = arg_t;
			     typ_strength = None;
			     typ_alias = sub} in
		  SEBfunctor(arg_id,arg_t,mte))
	      arg_entries mtb
	  in
	  None, Some sub_mtb
  in

  let mbids = List.map fst arg_entries in
    openmod_info:=(mbids,res_entry_o,sub_body_o);
  let prefix = Lib.start_module export id mp fs in
  Nametab.push_dir (Nametab.Until 1) (fst prefix) (DirOpenModule prefix);
  Lib.add_frozen_state (); mp


let end_module id =

  let oldoname,oldprefix,fs,lib_stack = Lib.end_module id in
  let mbids, res_o, sub_o = !openmod_info in
  let substitute, keep, special = Lib.classify_segment lib_stack in

  let dir = fst oldprefix in
  let msid = msid_of_prefix oldprefix in

  let substobjs, keep, special = try
    match res_o with
      | None -> 
	  (empty_subst, mbids, msid, substitute), keep, special
      | Some (MSEident ln) ->
	  abstract_substobjs mbids (MPmap.find ln (!modtypetab)), [], []
      | Some (MSEwith _ as mty) ->
	  abstract_substobjs mbids (get_modtype_substobjs (Global.env()) mty), [], []
      | Some (MSEfunctor _) -> 
	  anomaly "Funsig cannot be here..."
      | Some (MSEapply _ as mty) ->
	  abstract_substobjs mbids (get_modtype_substobjs (Global.env()) mty), [], []
  with
	Not_found -> anomaly "Module objects not found..."
  in
    (* must be called after get_modtype_substobjs, because of possible
     dependencies on functor arguments *)

  let mp = Global.end_module id res_o in

  begin match sub_o with
      None -> ()
    | Some sub_mtb -> check_subtypes mp sub_mtb
  end;

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
    mod_self_id * lib_objects * lib_objects


let register_library dir cenv objs digest =
  let mp = MPfile dir in
  let substobjs, objects =
    try 
      ignore(Global.lookup_module mp);
      (* if it's in the environment, the cached objects should be correct *)
      Dirmap.find dir !library_cache 
    with
	Not_found ->
	  if mp <> Global.import cenv digest then
	    anomaly "Unexpected disk module name";
	  let msid,substitute,keep = objs in
	  let substobjs = empty_subst, [], msid, substitute in
	  let substituted = subst_substobjs dir mp substobjs in
	  let objects = Option.map (fun seg -> seg@keep) substituted in
	  let modobjs = substobjs, objects in
	    library_cache := Dirmap.add dir modobjs !library_cache;
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
  let subst' = remove_alias subst in
  let mp' = subst_mp subst' mp in
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
  Lib.add_frozen_state (); mp


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
  if (mp_of_kn (snd oname)) <> ln then
    anomaly
      "Kernel and Library names do not match";

  Lib.add_frozen_state ()(* to prevent recaching *);
  ln


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
  let substobjs = get_modtype_substobjs (Global.env()) entry in
  (* Undo the simulated interactive building of the module type *)
  (* and declare the module type as a whole *)
  Summary.unfreeze_summaries fs;
    
  ignore (add_leaf id (in_modtype (Some entry, substobjs)));
  mmp
  with e ->
    (* Something wrong: undo the whole process *)
    Summary.unfreeze_summaries fs; raise e
			       

let rec get_module_substobjs env = function
  | MSEident mp -> MPmap.find mp !modtab_substobjs 
  | MSEfunctor (mbid,mty,mexpr) ->
       let (subst, mbids, msid, objs) = get_module_substobjs env mexpr in
	(subst, mbid::mbids, msid, objs)
  | MSEapply (mexpr, MSEident mp) ->
      let ftb,sub1 = Mod_typing.translate_struct_entry env mexpr in
      let farg_id, farg_b, fbody_b = Modops.destr_functor env 
	(Modops.eval_struct env ftb) in
      let mp = Environ.scrape_alias mp env in
      let sub_alias = (Environ.lookup_modtype mp env).typ_alias in
      let sub_alias = match Modops.eval_struct env (SEBident mp) with
	| SEBstruct (msid,sign) -> join_alias 
	    (subst_key (map_msid msid mp) sub_alias)
	      (map_msid msid mp)
	| _ -> sub_alias in

      let sub3=
	if sub1 = empty_subst then
	  update_subst sub_alias (map_mbid farg_id mp None)
	else
	  let sub1' = join_alias sub1 (map_mbid farg_id mp None) in
	  let sub_alias' =  update_subst sub_alias sub1' in
	    join sub1' sub_alias'
      in
      let sub3 = join sub3 (update_subst sub_alias (map_mbid farg_id mp None)) in
      let (subst, mbids, msid, objs) = get_module_substobjs env mexpr in
	(match mbids with
	   | mbid::mbids ->
               let resolve =
		 Modops.resolver_of_environment farg_id farg_b mp sub_alias env in
		 (* application outside the kernel, only for substitutive
                    objects (that are all non-logical objects) *)
		((join 
		    (join subst (map_mbid mbid mp (Some resolve)))
		       sub3)
		       , mbids, msid, objs)
	   | [] -> match mexpr with
	       | MSEident _  -> error "Application of a non-functor"
	       | _ -> error "Application of a functor with too few arguments")
  | MSEapply (_,mexpr) ->
      Modops.error_application_to_not_path mexpr
  | MSEwith (mty, With_Definition _) -> get_module_substobjs env mty
  | MSEwith (mty, With_Module (idl,mp)) -> 
      let substobjs = get_module_substobjs env mty in
      let modobjs = MPmap.find mp !modtab_substobjs in
	replace_module_object idl substobjs modobjs mp


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

let cache_include (oname,((me,is_mod),substobjs,substituted)) =
  let dir,mp1 = lift_oname oname in
  let prefix = (dir,(mp1,empty_dirpath)) in
    Global.add_include me;
    match substituted with
	Some seg -> 
	  load_objects 1 prefix seg;
	  open_objects 1 prefix seg; 
      | None ->  ()
	  
let load_include  i (oname,((me,is_mod),substobjs,substituted)) =
  let dir,mp1 = lift_oname oname in
  let prefix = (dir,(mp1,empty_dirpath)) in
    match substituted with
	Some seg -> 
	  load_objects i prefix seg
      | None ->  ()

let open_include i (oname,((me,is_mod),substobjs,substituted)) =
  let dir,mp1 = lift_oname oname in
  let prefix = (dir,(mp1,empty_dirpath)) in
    match substituted with
	Some seg -> 
	  if is_mod then
	  open_objects i prefix seg
	  else 
	    if i = 1 then	  
	      open_objects i prefix seg
      | None ->  ()

let subst_include (oname,subst,((me,is_mod),substobj,_)) =
  let dir,mp1 = lift_oname oname in
  let (sub,mbids,msid,objs) = substobj in
  let subst' = join sub subst in
  let substobjs = (subst',mbids,msid,objs) in
  let substituted = subst_substobjs dir mp1 substobjs in
    ((subst_inc_expr subst' me,is_mod),substobjs,substituted)

let classify_include (_,((me,is_mod),substobjs,_)) =
  Substitute ((me,is_mod),substobjs,None)

let (in_include,out_include) =
  declare_object {(default_object "INCLUDE") with
    cache_function = cache_include;
    load_function = load_include;
    open_function = open_include;
    subst_function = subst_include;
    classify_function = classify_include;
    export_function = (fun _ -> anomaly "No modules in section!") }

let rec update_include (sub,mbids,msid,objs) =
  let rec replace_include = function
    | [] -> [] 
    | (id,obj)::tail ->
	if object_tag obj = "INCLUDE" then
	  let ((me,is_mod),substobjs,substituted) = out_include obj in
	    if not (is_mod) then
	      let substobjs' = update_include substobjs in
                (id, in_include ((me,true),substobjs',substituted))::
		  (replace_include tail)
	    else
		  (id,obj)::(replace_include tail)
	else
	  (id,obj)::(replace_include tail)
  in
    (sub,mbids,msid,replace_include objs)
      
      
      
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
		(interp_modexpr (Global.env()) mexpr))
  in
  let entry = 
    {mod_entry_type = mty_entry_o;	    
     mod_entry_expr = mexpr_entry_o }
  in
  let env = Global.env() in
  let substobjs =
    match entry with
      | {mod_entry_type = Some mte} -> get_modtype_substobjs env mte
      | {mod_entry_expr = Some mexpr} -> get_module_substobjs env mexpr
      | _ -> anomaly "declare_module: No type, no body ..."
  in
  let substobjs = update_include substobjs in
    (* Undo the simulated interactive building of the module *)
    (* and declare the module as a whole *)
    Summary.unfreeze_summaries fs;
    match entry with 
      |{mod_entry_type = None;	    
	mod_entry_expr = Some (MSEident mp) } ->
	 let dir,mp' = dir_of_sp (Lib.make_path id), mp_of_kn (Lib.make_kn id) in
	 let (sub,mbids,msid,objs) = substobjs in
	 let mp1 = Environ.scrape_alias mp env in
	 let prefix =  dir,(mp1,empty_dirpath) in
	 let substituted = 
	   match mbids with
		    | [] -> 
			Some (subst_objects prefix 
				(join sub (join (map_msid msid mp1) (map_mp mp' mp1))) objs)
		    | _ -> None in
	   ignore (add_leaf
		     id
		     (in_module_alias (Some ({mod_entry_type = None;	    
					      mod_entry_expr = Some (MSEident mp1) }, mty_sub_o), 
				       substobjs, substituted)));
	   mmp
      | _ ->
	  let dir,mp = dir_of_sp (Lib.make_path id), mp_of_kn (Lib.make_kn id) in
	  let (sub,mbids,msid,objs) = substobjs in
	  let sub' = subst_key (map_msid msid mp) sub in
	  let substobjs = (join sub sub',mbids,msid,objs) in
	  let substituted = subst_substobjs dir mp substobjs in
	    ignore (add_leaf
		      id
		      (in_module (Some (entry, mty_sub_o), substobjs, substituted)));
	    mmp
	      
  with e -> 
    (* Something wrong: undo the whole process *)
    Summary.unfreeze_summaries fs; raise e
      

let declare_include interp_struct me_ast is_mod =

  let fs = Summary.freeze_summaries () in

    try 
      let env = Global.env() in
      let me = interp_struct env me_ast in 
      let substobjs = 	
	if is_mod then
	  get_module_substobjs env me
	else
	  get_modtype_substobjs env me in
      let mp1,_ = current_prefix () in
      let dir = dir_of_sp (Lib.path_of_include()) in
      let substituted = subst_substobjs dir mp1 substobjs in
      let id = current_mod_id() in
	
	ignore (add_leaf id
		  (in_include ((me,is_mod), substobjs, substituted)))
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
