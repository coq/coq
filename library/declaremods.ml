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
open Identifier
open Names
open Mod_declarations
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
    substitution * mod_bound_id list * mod_str_id * library_segment


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
	    Summary.survive_section = true }
(* TODO! Modtab survives section ? *)


(* if short=true adds short names to Nametab as well *)
let push_module_with_components sp mp short = 
  let (dir,id,_) = repr_path sp in
  let dir = dir@[id] in
  let names = 
    Modops.component_names 
      (Global.env ())
      (fun dir l -> dir@[ident_of_label l])
      (fun dir l -> Libnames.make_path dir (ident_of_label l) CCI)
      dir
      mp
  in
  let ref = ModRef mp in
    Nametab.push sp ref;
    Nametab.push_short_name id ref;
    
    if short then
      List.iter
	(fun (sp,ref) ->
	   if (dirpath sp) == dir then 
	     Nametab.push_short_name (basename sp) ref)
	names;
    List.iter (fun (sp,ref) -> Nametab.push sp ref) names
  

type modinfo_kind = 
  | ModObjects of module_path 
  | ModFull of module_path * module_entry


(* Interactive modules and module types cannot be recached! cache_mod*
   functions can be called only once (and "end_mod*" set the flag to
   false then)
*)

let recache_protection = ref true

let cache_module (sp,(l,info,substobjs,substituted,keep)) = 
  let mp = match info with
    | ModObjects mp -> 
	if !recache_protection then 
	  warning "You must not recache interactive modules!"
	else
	  recache_protection := true;
	mp
    | ModFull (mp,me) -> 
	let mp' = Global.add_module l me in
	  if mp<>mp' then
	    anomaly ("Expected and actual module paths do not match:" ^ 
		     string_of_modpath mp ^ "<>" ^ string_of_modpath mp')
	  else 
	    mp
  in
    if Nametab.exists_cci sp then 
      errorlabstrm "cache_module"
	(pr_id (basename sp) ++ str " already exists") ;
    
    push_module_with_components sp mp false;

    modtab := MPmap.add mp (substobjs,substituted,keep) !modtab;
    load_segment substituted;
    load_segment keep

(* When this function is called the module itself is already in the
   environment. This function loads its objects only *)
let load_module (_,(l,info,substobjs,substituted,keep)) = 
  let mp = match info with
    | ModObjects mp -> mp
    | ModFull (mp,_) -> 
	anomaly "We should never have full info in load_module!"
  in
    modtab := MPmap.add mp (substobjs,substituted,keep) !modtab;
    load_segment substituted;
    load_segment keep


let subst_substobjs mp ((subst,mbids,msid,objs) as substobjs) =
  match mbids with
    | [] -> subst_segment (add_msid msid mp subst) objs 
    | _ -> []


let subst_module subst (l,info,substobjs,_,keep) =
  (* calculate new path *)
  let mp = match info with
    | ModObjects mp -> subst_modpath subst mp
    | ModFull (mp,_) -> 
	anomaly "We should never have full info in subst_module!"
  in
  let (sub,mbids,msid,objs) = substobjs in
  let subst' = join sub subst in
  (* substitutive_objects get the new substitution *)
  let substobjs = (subst',mbids,msid,objs) in
  (* if we are not a functor - calculate substitued. 
     We add "msid |-> mp" to the substitution *)
  let substituted = subst_substobjs mp substobjs 
  in
    (l,ModObjects mp,substobjs,substituted,keep)


let classify_module (_,(l,info,substobjs,_,keep)) = 
  let info = match info with
    | ModObjects _ -> info
    | ModFull (mp,_) -> ModObjects mp
  in
    Substitute (l,info,substobjs,[],keep)

let (in_module,out_module) =
  declare_object {(default_object "MODULE") with   
    cache_function = cache_module;
    load_function = load_module;
    subst_function = subst_module;
    classify_function = classify_module;
    export_function = (fun _ -> anomaly "Old crap!!!") } 


(* we remember objects for a module type. In case of a declaration:
   Module M:SIG:=...
   The module M gets its objects from SIG
*)
let modtypetab = 
  ref (LNmap.empty : substitutive_objects LNmap.t)

(* currently begun interactive module type. We remember its arguments
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
				       modtypetab := LNmap.empty; 
				       openmodtype_info := []);
	    Summary.survive_section = true }




type modtypeinfo_kind =
  | ModtypeShort of long_name
  | ModtypeFull of long_name * module_type_entry


let cache_modtype (sp,(l,info,modtypeobjs)) = 
  let ln = match info with
    | ModtypeShort ln -> 
	if !recache_protection then 
	  warning "You must not recache interactive module types!"
	else
	  recache_protection := true;
	ln
    | ModtypeFull (ln,mte) -> 
	let ln' = Global.add_modtype l mte in
	  if ln<>ln' then
	    anomaly ("Expected and actual long names do not match:" ^ 
		     string_of_long_name ln ^ "<>" ^ 
		     string_of_long_name ln')
	  else
	    ln
  in
  let ref = ModTypeRef ln in
    if Nametab.exists_cci sp then 
      errorlabstrm "cache_modtype"
	(pr_id (basename sp) ++ str " already exists") ;
    Nametab.push sp ref;
    Nametab.push_short_name (basename sp) ref;
  
    modtypetab := LNmap.add ln modtypeobjs !modtypetab


let load_modtype (_,(_,info,modtypeobjs)) = 
  let ln = match info with
    | ModtypeShort ln -> ln
    | ModtypeFull _ ->
	anomaly "We should never have full info in load_modtype!"
  in
    modtypetab := LNmap.add ln modtypeobjs !modtypetab


let subst_modtype subst (l,info,(subs,mbids,msid,objs)) =
  let ln = match info with
    | ModtypeShort ln -> subst_long_name subst ln
    | ModtypeFull _ ->
	anomaly "We should never have full info in subst_modtype!"
  in
    (l,ModtypeShort ln,(join subs subst,mbids,msid,objs))


let classify_modtype (_,(l,info,substobjs)) = 
  let info = match info with
    | ModtypeShort _ -> info
    | ModtypeFull (ln,_) -> ModtypeShort ln
  in
    Substitute (l,info,substobjs)


let (in_modtype,out_modtype) =
    declare_object {(default_object "MODULE TYPE") with
      cache_function = cache_modtype;
      load_function = load_modtype;
      subst_function = subst_modtype;
      classify_function = classify_modtype;
      export_function = in_some } 



(*
let get_subst_libstack (subst,domlist,libstack) mplist = 
  let one_mp subst dom mp = match dom with
  | MPbid mbid -> add_mbid mbid mp subst
  | MPsid msid -> add_msid msid mp subst
  | _ -> anomaly "Not ident on the substitution list..." 
  in
  List.fold_left2 domlist mplist, libstack
*)
      

let abstract_substobjs mbids1 (subst, mbids2, msid, lib_stack) =
  (subst, mbids1@mbids2, msid, lib_stack)
  

let process_module sp mp short substobjs = 
  push_module_with_components sp mp short;
  let substituted = subst_substobjs mp substobjs in
    modtab := MPmap.add mp (substobjs,substituted,[]) !modtab;
    load_segment substituted


let rec get_modtype_substobjs = function
    MTEident ln -> LNmap.find ln !modtypetab
  | MTEfunsig (mbid,_,mte) -> 
      let (subst, mbids, msid, objs) = get_modtype_substobjs mte in
	(subst, mbid::mbids, msid, objs)
  | MTEsig (msid,_) -> (empty_subst, [], msid, []) 


(* push names of bound modules (and their components) to Nametab *)
(* add objects associated to them *)
let process_module_bindings argids args = 
  let process_arg id (mbid,mty) = 
    let sp = Libnames.make_path [] id CCI in
      if exists_cci sp then
	errorlabstrm "begin_module"
	  (pr_id (basename sp) ++ str " already exists");
      let mp = MPbid mbid in
	process_module sp mp false (get_modtype_substobjs mty)
  in
  List.iter2 process_arg argids args


let rec kill_keep objs = 
  let kill = function 
    | (sp,Leaf obj) as node ->
	if object_tag obj = "MODULE" then
	  let (l,info,substobjs,substitute,keep) = out_module obj in
	    match substitute,keep with
	      | [],[] -> node 
	      | _ -> sp, Leaf (in_module (l,info,substobjs,[],[]))
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

let begin_module l argids args res_o = 
  Global.begin_module l args res_o;
  let mbids = List.map fst args in
  let fs = Summary.freeze_summaries () in
    process_module_bindings argids args;
    openmod_info:=(mbids,res_o);
    ignore (Lib.begin_module (ident_of_label l) fs);
    Lib.add_frozen_state ()


let end_module l =
  (* we prepare the info to perform the lib_stack calculation *)
  let msid = Global.current_msid () in
  let mbids, res_o = !openmod_info in

  let mp = Global.end_module l in
  let sp,dir,fs,substitute,keep,special = Lib.end_module (ident_of_label l) in
  Summary.unfreeze_other_summaries fs;
    
  let substobjs,substituted,keep = match res_o with
      None -> 
	(* we kill_keeps in submodules to store them in substobjs, 
	   but leave them in substituted ! *)
	let substitute' = kill_keep substitute in
	let substobjs = (empty_subst, mbids, msid, substitute') in
	  (match mbids with
	    | [] ->   
		let substituted = 
		  subst_segment (map_msid msid mp) substitute (* no ' *)
		in
		  substobjs, substituted, keep
	    | _ ->
		substobjs,[],[])

    | Some (MTEident ln) ->
	let substobjs = 
	  abstract_substobjs mbids (LNmap.find ln (!modtypetab))
	in
	  substobjs, subst_substobjs mp substobjs, []
		    
    | Some (MTEsig (msid,_)) ->
	(empty_subst, mbids, msid, []), [], []
    | _ -> anomaly "Funsig cannot be here..."

  in
    
    recache_protection := false;
    let sp' = Lib.add_leaves
		special
		(ident_of_label l) 
		CCI
	        (in_module (l,ModObjects mp,substobjs,substituted,keep)) 
    in
    if sp <> sp' then 
      anomaly 
	"Section paths generated on begin_ and end_module do not match";
    Lib.add_frozen_state () (* to prevent recaching *)


type comp_unit_name = dir_path

type comp_unit = { 
  md_name : comp_unit_name;
  md_compiled_env : Safe_env.compiled_module;
  md_objects : mod_str_id * library_segment * library_segment}

(*

Having this module_cache here is not nice. The information from the
cache should rather be placed in the "REQUIRE" or "READ" object. To
this end we have to traverse the dependencies (in library) and
calculate all objects (here) in the preparation phase and not in cache
phase - i.e. before Lib.add_leaf



type comp_unit_objects = module_path * module_objects

let calculate_objects md = let mp = MPcomp md.md_name in let
  msid,substitute,keep = md.md_objects in let substitute' = kill_keep
  substitute in let substobjs = (empty_subst, [], msid, substitute')
  in let substituted = subst_segment (map_msid msid mp) substitute (*
  no ' *) in let module_objects = substobjs, substituted, keep in mp,
  module_objects


let register_comp_unit

*)



let module_cache = Hashtbl.create 17

let register_comp_unit md digest =
  let mp = MPcomp md.md_name in
  if mp <> Global.import md.md_compiled_env digest then 
    anomaly "Unexpected disk module name";
  let msid,substitute,keep = md.md_objects in
  let substitute' = kill_keep substitute in
  let substobjs = (empty_subst, [], msid, substitute') in
  let substituted = 
    subst_segment (map_msid msid mp) substitute (* no ' *)
  in
  let module_objects = substobjs, substituted, keep in

  Hashtbl.add module_cache md.md_name module_objects;

  modtab:=MPmap.add mp module_objects !modtab;
    
  Nametab.push_loaded_library md.md_name;
    (* TODO: revise this! *)
  push_module_with_components (sp_of_wd md.md_name) mp false;
  Lib.load_segment substituted;
  Lib.load_segment keep



let re_register_comp_unit dir = 
  let mp = MPcomp dir in
  (try 
     ignore(Global.lookup_module mp) 
   with
     Not_found -> 
       anomaly "The module should be in the environment!");
  let (substobjs, substituted, keep) as module_objects = 
    try 
      Hashtbl.find module_cache dir 
    with
      Not_found -> 
	anomaly "The module objects should be in the cache!"
  in
  modtab:=MPmap.add mp module_objects !modtab;
    
  Nametab.push_loaded_library dir;
    (* TODO: revise this! *)
  push_module_with_components (sp_of_wd dir) mp false;
  Lib.load_segment substituted;
  Lib.load_segment keep

   

let import_module mp = 
  let sp = get_sp (ModRef mp) in
    push_module_with_components sp mp true; 
    let (_,substituted,keep) = MPmap.find mp !modtab in
      open_segment substituted;
      open_segment keep



let begin_modtype l argids args = 
  Global.begin_modtype l args;
  let fs= Summary.freeze_summaries () in
    process_module_bindings argids args;
    openmodtype_info := (List.map fst args);
    ignore (Lib.begin_modtype (ident_of_label l) fs);
    Lib.add_frozen_state ()
      (* TODO: finish ! *)

let end_modtype l =
  let msid = Global.current_msid () in
  let mbids = !openmodtype_info in

  let ln = Global.end_modtype l in
  let sp,dir,fs,lib_stack,special = Lib.end_modtype (ident_of_label l) in
  Summary.unfreeze_other_summaries fs;

  recache_protection := false;
  let modtypeobjs = empty_subst, mbids, msid, lib_stack in 
  let sp' = Lib.add_leaves 
	      special
	      (ident_of_label l)
	      (CCI)
              (in_modtype (l, ModtypeShort ln, modtypeobjs))
  in
  if sp <> sp' then 
    anomaly 
      "Section paths generated on begin_ and end_modtype do not match";
    
		
  Lib.add_frozen_state ()


	     

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

let declare_module l me = 
  let substobjs = 
    match me with
      | {mod_entry_type = Some mte} -> get_modtype_substobjs mte
      | {mod_entry_expr = Some mexpr} -> get_module_substobjs mexpr
      | _ -> anomaly "declare_module: No type, no body ..." 
  in
  let mp = MPdot(Global.current_modpath (),l) in
  let substituted = subst_substobjs mp substobjs in
    ignore (add_leaf 
	      (ident_of_label l) 
	      (CCI) 
	      (in_module (l, ModFull (mp,me), substobjs, substituted, [])))



(*let inductive_names_from_body sp ln mib =
  let names, _ = 
    Array.fold_left
      (fun (names, n) ind ->
	 let ind_p = (ln,n) in
	 let names, _ =
	   Array.fold_left
	     (fun (names, p) l ->
		let sp = 
		  Libnames.make_path (dirpath sp) (ident_of_label l) CCI 
		in
		  ((sp, ConstructRef (ind_p,p)) :: names, p+1))
	     (names, 1) ind.mind_consnames in
	 let sp = 
	   Libnames.make_path 
	     (dirpath sp) 
	     (ident_of_label ind.mind_typename) 
	     CCI 
	 in
	   ((sp, IndRef ind_p) :: names, n+1))
      ([], 0) mib.mind_packets
  in names
*)


let debug_print_modtab _ = 
  let pr_seg = function
    | [] -> str "[]"
    | l -> str ("[." ^ string_of_int (List.length l) ^ ".]")
  in
  let pr_modinfo mp (_,substituted,keep) s = 
    s ++ (pr_modpath mp) ++ (spc ()) 
    ++ (pr_seg substituted) ++ (spc ()) 
    ++ pr_seg keep ++ (fnl ()) 
  in
  let modules = MPmap.fold pr_modinfo !modtab (mt ()) in
    hov 0 modules

  
