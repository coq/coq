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

let modtab = 
  ref (MPmap.empty  :
	 (substitution * mod_bound_id list * mod_self_id * library_segment) 
	 MPmap.t)
    
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

let modtypetab = 
  ref (KNmap.empty :
	 (substitution * mod_bound_id list * mod_self_id * library_segment) 
	 KNmap.t)

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

let component_names env make_dir make_path dir mp =

  let inductive_names_from_body dir ln mib names =
    let names, _ = 
      Array.fold_left
	(fun (names, n) ind ->
	   let ind_p = (ln,n) in
	   let names, _ =
	     Array.fold_left
	       (fun (names, p) l ->
		let sp = make_path dir l in
		  ((sp, ConstructRef (ind_p,p)) :: names, p+1))
	       (names, 1) ind.mind_consnames in
	   let sp = make_path dir ind.mind_typename in
	     ((sp, IndRef ind_p) :: names, n+1))
	(names, 0) mib.mind_packets
    in names
	 
  in
    
  let rec process_signature dir mp sign names = 
    let process_one names (l,elem) =
      let kn = Names.make_kn mp empty_dirpath l in
      let path = make_path dir (id_of_label l) in
	match elem with
	  | SPBconst _ -> (path,ConstRef kn)::names
	  | SPBmind mib -> 
	      inductive_names_from_body dir kn mib names
	  | SPBmodule _ -> 
	      let mp' = MPdot (mp,l) in
	      let dir' = make_dir dir l in
	      let names' = (*(path, ModRef mp')::*)names in
		process_module dir' mp' names'
	  | SPBmodtype mtb -> 
	      (*(path, ModTypeRef ln)::*)names
    in
      List.fold_left process_one names sign
	
  and process_module dir mp names = 
    let mb = Environ.lookup_module mp env in
      match Modops.scrape_modtype env mb.mod_type with
	| MTBident _ -> anomaly "scrape_modtype does not work!"
	| MTBsig (_,sign) -> 
	    process_signature dir mp sign names 
	| MTBfunsig _ -> names

  in
    List.rev (process_module dir mp [])


(* if short=true adds short names to Nametab as well *)
let push_module_with_components dir mp short = 
  let names = 
    component_names 
      (Global.env ())
      (fun dir l -> extend_dirpath dir (id_of_label l))
      (fun dir l -> Libnames.make_path dir l)
      dir
      mp
  in
(*  let ref = ModRef mp in
    Nametab.push sp ref;
    Nametab.push_short_name id ref; *)
    
    List.iter (fun (sp,ref) -> Nametab.push 0 sp ref) names
(*    if short then
      List.iter
	(fun (sp,ref) ->
	   if (dirpath sp) == dir then 
	     Nametab.push_short_name (basename sp) ref)
	names
  *)
    

(*
let get_subst_libstack (subst,domlist,libstack) mplist = 
  let one_mp subst dom mp = match dom with
  | MPbid mbid -> add_mbid mbid mp subst
  | MPsid msid -> add_msid msid mp subst
  | _ -> anomaly "Not ident on the substitution list..." 
  in
  List.fold_left2 domlist mplist, libstack

      

let abstract_libstack mbids1 (subst, mbids2, msid, lib_stack) =
  (subst, mbids1@mbids2, msid, lib_stack)
  

type modtype_genesis =
  | InteractiveModtype of long_name
  | RegularModtype of module_type_entry


(* Interactive modules and module types cannot be recached! cache_mod*
   functions can be called only once (and "end_mod*" set the flag to
   false then)
*)

let recache_protection = ref true

let cache_modtype (sp,(l,mtg,modtypeobjs)) = 
  let ln = match mtg with
    | InteractiveModtype ln -> 
	if !recache_protection then 
	  warning "You must not recache interactive module types!"
	else
	  recache_protection := true;
	ln
    | RegularModtype mte -> Global.add_modtype l mte
  in
  let ref = ModTypeRef ln in
  Nametab.push sp ref;
  Nametab.push_short_name (basename sp) ref;
  
  modtypetab := KNmap.add ln modtypeobjs !modtypetab


let (in_modtype,out_modtype) =
    declare_object {(default_object "MODULE TYPE") with
      cache_function = cache_modtype;
      export_function = in_some } 


type module_genesis = 
  | InteractiveMod of module_path 
  | RegularMod of module_entry


let (out_module_hack :  
     (Libobject.obj ->
	label * module_genesis *
	(substitution * mod_bound_id list *mod_str_id *
	 library_segment)) ref)
= 
  ref (fun _ -> anomaly "Out module forward declaration")

let rec cache_module (sp,(l,mg,modobjs)) = 
  let mp = match mg with
    | InteractiveMod mp -> 
	if !recache_protection then 
	  warning "You must not recache interactive modules!"
	else
	  recache_protection := true;
	mp
    | RegularMod me -> Global.add_module l me
  in
    if Nametab.exists_cci sp then 
      errorlabstrm "cache_module"
	(pr_id (basename sp) ++ str " already exists") ;
    
    process_module sp mp false modobjs


(* add_modobjs adds "mp |-> modobjs" to modtab, and processes 
   all objects in modobjs:
   - cache_subst's regular objects,
   - recursively processes sub-modules,
   - updates module type object information
*)
and add_modobjs mp ((subst,mbids,msid,lib_stack) as modobjs) = 
  let process_node subst' (sp,node) = 
    let lobj = match node with
      | Leaf obj -> obj
      | _ -> anomaly "We should only have leafs here!"
    in
    let tag = Libobject.object_tag lobj in
      match tag with 
	| "MODULE" -> 
	    let (l,_,modobjs) = !out_module_hack lobj in
	    let (subst,mbids,msid,lib_stack) = modobjs in
	    let mp' = MPdot(mp,l) in
	    let subst'' = Names.join subst subst' in
	      add_modobjs mp' (subst'',mbids,msid,lib_stack)

	| "MODULE TYPE" ->
	    let (l,_,modtypeobjs) = out_modtype lobj in
	    let (subst,mbids,msid,lib_stack) = modtypeobjs in
	    let ln = make_ln mp l in
	    let subst'' = Names.join subst subst' in
	      modtypetab := KNmap.add ln (subst'',mbids,msid,lib_stack)
		!modtypetab;
	      
	| _ -> Libobject.cache_subst_object (sp,lobj,subst')
  in
    modtab := MPmap.add mp modobjs !modtab;
    if mbids=[] then (* if this is a structure *)
      List.iter (process_node (add_msid msid mp subst)) lib_stack
      
and process_module sp mp short modobjs = 
  push_module_with_components sp mp short;
  add_modobjs mp modobjs


let (in_module,out_module) =
  declare_object {(default_object "MODULE") with   
    cache_function = cache_module;
    export_function = in_some } 

let _ = out_module_hack := out_module


let rec get_modtype_libstack = function
    MTEident ln -> KNmap.find ln !modtypetab
  | MTEfunsig (mbid,_,mte) -> 
      let (subst, mbids, msid, libstack) = get_modtype_libstack mte in
	(subst, mbid::mbids, msid, libstack)
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
	process_module sp mp false (get_modtype_libstack mty)
  in
  List.iter2 process_arg argids args


let begin_module l argids args res_o = 
  Global.begin_module l args res_o;
  let mbids = List.map fst args in
  let fs = Summary.freeze_summaries () in
    process_module_bindings argids args;
    openmod_info:=(mbids,res_o);
    ignore (Lib.open_module (ident_of_label l) fs);
    Lib.add_frozen_state ()


let end_module l =
  (* we prepare the info to perform the lib_stack calculation *)
  let msid = Global.current_msid () in
  let mbids, res_o = !openmod_info in

  let mp = Global.end_module l in
  let sp,dir,fs,lib_stack = Lib.close_module (ident_of_label l) in
  Summary.unfreeze_other_summaries fs;
    
  let modobjs = match res_o with
      None -> (empty_subst, mbids, msid, lib_stack)
    | Some (MTEident ln) ->
	abstract_libstack mbids (KNmap.find ln (!modtypetab))
    | Some (MTEsig (msid,_)) ->
	(empty_subst, mbids, msid, [])
    | _ -> anomaly "Funsig cannot be here..."

  in
    
    recache_protection := false;
    let sp' = Lib.add_leaf 
		(ident_of_label l) 
		CCI
	        (in_module (l,InteractiveMod mp,modobjs)) 
    in
    if sp <> sp' then 
      anomaly 
	"Section paths generated on begin_ and end_module do not match";
    Lib.add_frozen_state () (* to prevent recaching *)





let begin_modtype l argids args = 
  Global.begin_modtype l args;
  let fs= Summary.freeze_summaries () in
    process_module_bindings argids args;
    openmodtype_info := (List.map fst args);
    ignore (Lib.open_modtype (ident_of_label l) fs);
    Lib.add_frozen_state ()
      (* TODO: finish ! *)

let end_modtype l =
  let msid = Global.current_msid () in
  let mbids = !openmodtype_info in

  let ln = Global.end_modtype l in
  let sp,dir,fs,lib_stack = Lib.close_modtype (ident_of_label l) in
  Summary.unfreeze_other_summaries fs;

  recache_protection := false;
  let modtypeobjs = empty_subst, mbids, msid, lib_stack in 
  let sp' = Lib.add_leaf 
	      (ident_of_label l)
	      (CCI)
              (in_modtype (l, InteractiveModtype ln, modtypeobjs))
  in
  if sp <> sp' then 
    anomaly 
      "Section paths generated on begin_ and end_modtype do not match";
    
		
  Lib.add_frozen_state ()


	     

let rec get_module_libstack = function
    MEident mp -> MPmap.find mp !modtab
  | MEfunctor (mbid,_,mexpr) -> 
      let (subst, mbids, msid, libstack) = get_module_libstack mexpr in
	(subst, mbid::mbids, msid, libstack)
  | MEstruct (msid,_) ->
      (empty_subst, [], msid, [])
  | MEapply (mexpr, MEident mp) ->
      let (subst, mbids, msid, libstack) = get_module_libstack mexpr in
	(match mbids with
	   | mbid::mbids -> 
	       (add_mbid mbid mp subst, mbids, msid, libstack)
	   | [] -> anomaly "Too few arguments in functor")
  | MEapply (_,_) -> anomaly "The argument must be an identifier!"


let declare_module l me = 
  let (subst, mbids, msid, libstack) as modobjs = 
    match me with
      | {mod_entry_type = Some mte} -> get_modtype_libstack mte
      | {mod_entry_expr = Some mexpr} -> get_module_libstack mexpr
      | _ -> anomaly "declare_module: No type, no body ..." 
  in
    ignore (add_leaf 
	      (ident_of_label l) 
	      (CCI) 
	      (in_module (l, RegularMod me, modobjs)))



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
  let pr_modinfo mp _ str = str ++ (pr_modpath mp) ++ (fnl ()) in
  let modules = MPmap.fold pr_modinfo !modtab (mt ()) in
    v 0 modules

  
*)
