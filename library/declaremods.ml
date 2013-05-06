(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Names
open Declarations
open Entries
open Libnames
open Libobject
open Lib
open Mod_subst
open Vernacexpr

let scope_subst = ref (String.Map.empty : string String.Map.t)

let add_scope_subst sc sc' =
  scope_subst := String.Map.add sc sc' !scope_subst

let register_scope_subst scl =
  List.iter (fun (sc1,sc2) -> add_scope_subst sc1 sc2) scl

let subst_scope sc =
 try String.Map.find sc !scope_subst with Not_found -> sc

let reset_scope_subst () =
  scope_subst := String.Map.empty

let default_inline () = Some (Flags.get_inline_level ())

let inl2intopt = function
  | NoInline -> None
  | InlineAt i -> Some i
  | DefaultInline -> default_inline ()

let inline_annot a = inl2intopt a.ann_inline

(* modules and components *)

(* This type is for substitutive lib_objects.

   The first part is a list of bound identifiers which is nonempty
   only if the objects are owned by a fuctor

   The second one is the "self" ident of the signature (or structure),
   which should be substituted in lib_objects with the real name of
   the module.

   The third one is the segment itself. *)

type substitutive_objects =
     MBId.t list * module_path * lib_objects


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
  Summary.ref (MPmap.empty : substitutive_objects MPmap.t)
    ~name:"MODULE-INFO-1"

let modtab_objects =
  Summary.ref (MPmap.empty : (object_prefix * lib_objects) MPmap.t)
    ~name:"MODULE-INFO-2"

type current_module_info = {
  cur_mp : module_path; (** current started interactive module (if any) *)
  cur_args : MBId.t list; (** its arguments *)
  cur_typ : (module_struct_entry * int option) option; (** type via ":" *)
  cur_typs : module_type_body list (** types via "<:" *)
}

let default_module_info =
  { cur_mp = MPfile DirPath.initial;
    cur_args = [];
    cur_typ = None;
    cur_typs = [] }

let openmod_info = Summary.ref default_module_info ~name:"MODULE-INFO-3"

(* The library_cache here is needed to avoid recalculations of
   substituted modules object during "reloading" of libraries *)
let library_cache = Summary.ref Dirmap.empty ~name:"MODULE-INFO-4"

(* auxiliary functions to transform full_path and kernel_name given
   by Lib into module_path and DirPath.t needed for modules *)

let mp_of_kn kn =
  let mp,sec,l = repr_kn kn in
    if DirPath.is_empty sec then
      MPdot (mp,l)
    else
      anomaly (str "Non-empty section in module name!" ++ spc () ++ pr_kn kn)

let dir_of_sp sp =
  let dir,id = repr_path sp in
    add_dirpath_suffix dir id

(* Subtyping checks *)

let check_sub mtb sub_mtb_l =
  (* The constraints are checked and forgot immediately : *)
  ignore (List.fold_right
	    (fun sub_mtb env ->
	       Environ.add_constraints
		 (Subtyping.check_subtypes env mtb sub_mtb) env)
	    sub_mtb_l (Global.env()))

(* This function checks if the type calculated for the module [mp] is
   a subtype of all signatures in [sub_mtb_l]. Uses only the global
   environment. *)

let check_subtypes mp sub_mtb_l =
  let mb =
    try Global.lookup_module mp
    with Not_found -> assert false
  in
  let mtb = Modops.module_type_of_module None mb in
  check_sub mtb sub_mtb_l

(* Same for module type [mp] *)

let check_subtypes_mt mp sub_mtb_l =
  let mtb =
    try Global.lookup_modtype mp
    with Not_found -> assert false
  in
  check_sub mtb sub_mtb_l

(* Create a functor type entry *)

let funct_entry args m =
  List.fold_right
    (fun (arg_id,(arg_t,_)) mte -> MSEfunctor (arg_id,arg_t,mte))
    args m

(* Prepare the module type list for check of subtypes *)

let build_subtypes interp_modtype mp args mtys =
  List.map
    (fun (m,ann) ->
       let inl = inline_annot ann in
       let mte = interp_modtype (Global.env()) m in
       let mtb = Mod_typing.translate_module_type (Global.env()) mp inl mte in
       let funct_mtb =
	 List.fold_right
           (fun (arg_id,(arg_t,arg_inl)) mte ->
              let arg_t =
		Mod_typing.translate_module_type (Global.env())
		  (MPbound arg_id) arg_inl arg_t
	      in
              SEBfunctor(arg_id,arg_t,mte))
           args mtb.typ_expr
       in
       { mtb with typ_expr = funct_mtb })
    mtys


(* These functions register the visibility of the module and iterates
   through its components. They are called by plenty module functions *)

let compute_visibility exists what i dir dirinfo =
  if exists then
    if
      try
        let globref = Nametab.locate_dir (qualid_of_dirpath dir) in
        eq_global_dir_reference globref dirinfo
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

let do_module exists what iter_objects i dir mp substobjs keep =
  let prefix = (dir,(mp,DirPath.empty)) in
  let dirinfo = DirModule prefix in
  let vis = compute_visibility exists what i dir dirinfo in
  Nametab.push_dir vis dir dirinfo;
  modtab_substobjs := MPmap.add mp substobjs !modtab_substobjs;
  match substobjs with
    | ([],mp1,objs) ->
      modtab_objects := MPmap.add mp (prefix,objs@keep) !modtab_objects;
      iter_objects (i+1) prefix (objs@keep)
    | (mbids,_,_) -> ()

let conv_names_do_module exists what iter_objects i ((sp,kn),substobjs) =
  let dir = dir_of_sp sp and mp = mp_of_kn kn in
  do_module exists what iter_objects i dir mp substobjs []

(* Nota: Interactive modules and module types cannot be recached!
   This used to be checked here via a flag along the substobjs.
   The check is still there for module types (see cache_modtype). *)

let cache_module ((sp,kn),substobjs) =
  let dir = dir_of_sp sp and mp = mp_of_kn kn in
  do_module false "cache" load_objects 1 dir mp substobjs []

(* When this function is called the module itself is already in the
   environment. This function loads its objects only *)

let load_module i oname_substobjs =
  conv_names_do_module false "load" load_objects i oname_substobjs

let open_module i oname_substobjs =
  conv_names_do_module true "open" open_objects i oname_substobjs

let subst_module (subst,(mbids,mp,objs)) =
  (mbids, subst_mp subst mp, subst_objects subst objs)

let classify_module substobjs = Substitute substobjs

let (in_module : substitutive_objects -> obj),
    (out_module : obj -> substitutive_objects) =
  declare_object_full {(default_object "MODULE") with
    cache_function = cache_module;
    load_function = load_module;
    open_function = open_module;
    subst_function = subst_module;
    classify_function = classify_module }

let cache_keep _ = anomaly (Pp.str "This module should not be cached!")

let load_keep i ((sp,kn),seg) =
  let mp = mp_of_kn kn in
  let prefix = dir_of_sp sp, (mp,DirPath.empty) in
    begin
      try
	let prefix',objects = MPmap.find mp !modtab_objects in
	  if not (eq_op prefix' prefix) then
	    anomaly (Pp.str "Two different modules with the same path!");
	  modtab_objects := MPmap.add mp (prefix,objects@seg) !modtab_objects;
      with
	  Not_found -> anomaly (Pp.str "Keep objects before substitutive")
    end;
    load_objects i prefix seg

let open_keep i ((sp,kn),seg) =
  let dirpath,mp = dir_of_sp sp, mp_of_kn kn in
    open_objects i (dirpath,(mp,DirPath.empty)) seg

let in_modkeep : lib_objects -> obj =
  declare_object {(default_object "MODULE KEEP OBJECTS") with
    cache_function = cache_keep;
    load_function = load_keep;
    open_function = open_keep }

(* we remember objects for a module type. In case of a declaration:
   Module M:SIG:=...
   The module M gets its objects from SIG
*)
let modtypetab =
  Summary.ref (MPmap.empty : substitutive_objects MPmap.t)
    ~name:"MODTYPE-INFO-1"

(* currently started interactive module type. We remember its arguments
   if it is a functor type *)
let openmodtype_info =
  Summary.ref ([],[] : MBId.t list * module_type_body list)
    ~name:"MODTYPE-INFO-2"

let cache_modtype ((sp,kn),(entry,modtypeobjs,sub_mty_l)) =
  let mp = mp_of_kn kn in

  (* We enrich the global environment *)
  let _ = match entry with
    | None -> anomaly (Pp.str "You must not recache interactive module types!")
    | Some (mte,inl) ->
      if not (ModPath.equal mp (Global.add_modtype (basename sp) mte inl)) then
	anomaly (Pp.str "Kernel and Library names do not match")
  in

  (* Using declare_modtype should lead here, where we check
     that any given subtyping is indeed accurate *)
  check_subtypes_mt mp sub_mty_l;

  if Nametab.exists_modtype sp then
    errorlabstrm "cache_modtype"
      (pr_path sp ++ str " already exists") ;

  Nametab.push_modtype (Nametab.Until 1) sp mp;

  modtypetab := MPmap.add mp modtypeobjs !modtypetab


let load_modtype i ((sp,kn),(entry,modtypeobjs,_)) =
  assert (Option.is_empty entry);

  if Nametab.exists_modtype sp then
    errorlabstrm "cache_modtype"
      (pr_path sp ++ str " already exists") ;

  Nametab.push_modtype (Nametab.Until i) sp (mp_of_kn kn);

  modtypetab := MPmap.add (mp_of_kn kn) modtypeobjs !modtypetab


let open_modtype i ((sp,kn),(entry,_,_)) =
  assert (Option.is_empty entry);

  if
    try
      let mp = Nametab.locate_modtype (qualid_of_path sp) in
      not (ModPath.equal mp (mp_of_kn kn))
    with Not_found -> true
  then
    errorlabstrm ("open_modtype")
      (pr_path sp ++ str " should already exist!");

  Nametab.push_modtype (Nametab.Exactly i) sp (mp_of_kn kn)

let subst_modtype (subst,(entry,(mbids,mp,objs),_)) =
  assert (Option.is_empty entry);
  (entry,(mbids,subst_mp subst mp,subst_objects subst objs),[])

let classify_modtype (_,substobjs,_) =
  Substitute (None,substobjs,[])

type modtype_obj =
    (module_struct_entry * Entries.inline) option (* will be None in vo *)
    * substitutive_objects
    * module_type_body list

let in_modtype : modtype_obj -> obj =
    declare_object {(default_object "MODULE TYPE") with
      cache_function = cache_modtype;
      open_function = open_modtype;
      load_function = load_modtype;
      subst_function = subst_modtype;
      classify_function = classify_modtype }

let rec replace_module_object idl (mbids,mp,lib_stack) (mbids2,mp2,objs) mp1 =
  let () = match mbids with
  | [] -> () | _ -> anomaly (Pp.str "Unexpected functor objects") in
  let rec replace_idl = function
    | _,[] -> []
    | id::idl,(id',obj)::tail when Id.equal id id' ->
      if not (String.equal (object_tag obj) "MODULE") then anomaly (Pp.str "MODULE expected!");
      let substobjs = match idl with
      | [] ->
        let mp' = MPdot(mp, Label.of_id id) in
        mbids, mp', subst_objects (map_mp mp1 mp' empty_delta_resolver) objs
      | _ ->
        replace_module_object idl (out_module obj) (mbids2,mp2,objs) mp
      in
      (id, in_module substobjs)::tail
    | idl,lobj::tail -> lobj::replace_idl (idl,tail)
  in
  (mbids, mp, replace_idl (idl,lib_stack))

let discr_resolver mb = match mb.mod_type with
  | SEBstruct _ -> Some mb.mod_delta
  | _ -> None (* when mp is a functor *)

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

let rec compute_subst env mbids sign mp_l inl =
  match mbids,mp_l with
    | _,[] -> mbids,empty_subst
    | [],r -> error "Application of a functor with too few arguments."
    | mbid::mbids,mp::mp_l ->
	let farg_id, farg_b, fbody_b = Modops.destr_functor env sign in
	let mb = Environ.lookup_module mp env in
	let mbid_left,subst = compute_subst env mbids fbody_b mp_l inl in
	let resolver = match discr_resolver mb with
	  | None -> empty_delta_resolver
	  | Some mp_delta ->
	      Modops.inline_delta_resolver env inl mp farg_id farg_b mp_delta
	in
	mbid_left,join (map_mbid mbid mp resolver) subst

let rec get_modtype_substobjs env inline = function
  | MSEident ln ->
      MPmap.find ln !modtypetab
  | MSEfunctor (mbid,_,mte) ->
      let (mbids, mp, objs) = get_modtype_substobjs env inline mte in
      (mbid::mbids, mp, objs)
  | MSEwith (mty, With_Definition _) ->
      get_modtype_substobjs env inline mty
  | MSEwith (mty, With_Module (idl,mp1)) ->
      let substobjs = get_modtype_substobjs env inline mty in
      let modobjs = MPmap.find mp1 !modtab_substobjs in
      replace_module_object idl substobjs modobjs mp1
  | MSEapply (fexpr, MSEident mp) as me ->
      let (mbids, mp1, objs),mtb_mp1,mp_l =
	get_objs_modtype_application env me in
      let mbids_left,subst =
	compute_subst env mbids mtb_mp1.typ_expr (List.rev mp_l) inline
      in
      (mbids_left, mp1,subst_objects subst objs)
  | MSEapply (_,mexpr) ->
      Modops.error_application_to_not_path mexpr

(* push names of a bound module (and its component) to Nametab *)
(* add objects associated to it *)
let process_module_binding mbid mty =
  let dir = DirPath.make [MBId.to_id mbid] in
  let mp = MPbound mbid in
  let (mbids,mp_from,objs) =
    get_modtype_substobjs (Global.env()) (default_inline ()) mty
  in
  let subst = map_mp mp_from mp empty_delta_resolver in
  let substobjs = (mbids,mp,subst_objects subst objs) in
  do_module false "start" load_objects 1 dir mp substobjs []

(* Same with module_type_body *)

let rec seb2mse = function
  | SEBident mp -> MSEident mp
  | SEBapply (s,s',_) -> MSEapply(seb2mse s, seb2mse s')
  | SEBwith (s,With_module_body (l,mp)) -> MSEwith(seb2mse s,With_Module(l,mp))
  | SEBwith (s,With_definition_body(l,cb)) ->
      (match cb.const_body with
	| Def c -> MSEwith(seb2mse s,With_Definition(l,Lazyconstr.force c))
	| _ -> assert false)
  | _ -> failwith "seb2mse: received a non-atomic seb"

let process_module_seb_binding mbid seb =
  process_module_binding mbid (seb2mse seb)

let intern_args interp_modtype (idl,(arg,ann)) =
  let inl = inline_annot ann in
  let lib_dir = Lib.library_dp() in
  let env = Global.env() in
  let mty = interp_modtype env arg in
  let (mbi,mp_from,objs) = get_modtype_substobjs env inl mty in
  List.map
    (fun (_,id) ->
      let dir = DirPath.make [id] in
      let mbid = MBId.make lib_dir id in
      let mp = MPbound mbid in
      let resolver = Global.add_module_parameter mbid mty inl in
      let subst = map_mp mp_from mp resolver in
      let substobjs = (mbi,mp,subst_objects subst objs) in
      do_module false "interp" load_objects 1 dir mp substobjs [];
      (mbid,(mty,inl)))
    idl

let start_module_ interp_modtype export id args res fs =
  let mp = Global.start_module id in
  let arg_entries = List.concat (List.map (intern_args interp_modtype) args) in
  let res_entry_o, subtyps = match res with
    | Enforce (res,ann) ->
        let inl = inline_annot ann in
	let mte = interp_modtype (Global.env()) res in
	let _ = Mod_typing.translate_struct_type_entry (Global.env()) inl mte in
	Some (mte,inl), []
    | Check resl ->
	None, build_subtypes interp_modtype mp arg_entries resl
  in
  let mbids = List.map fst arg_entries in
  openmod_info:=
    { cur_mp = mp;
      cur_args = mbids;
      cur_typ = res_entry_o;
      cur_typs = subtyps };
  let prefix = Lib.start_module export id mp fs in
  Nametab.push_dir (Nametab.Until 1) (fst prefix) (DirOpenModule prefix);
  Lib.add_frozen_state (); mp


let end_module () =
  let oldoname,oldprefix,fs,lib_stack = Lib.end_module () in
  let substitute, keep, special = Lib.classify_segment lib_stack in
  let m_info = !openmod_info in

  let mp_from, substobjs, keep, special =
    match m_info.cur_typ with
      | None ->
	  (* the module is not sealed *)
	  None, (m_info.cur_args, m_info.cur_mp, substitute), keep, special
      | Some (MSEfunctor _, _) -> anomaly (Pp.str "Funsig cannot be here...")
      | Some (mty, inline) ->
	  let (mbids1,mp1,objs) =
            try get_modtype_substobjs (Global.env()) inline mty
            with Not_found -> anomaly (Pp.str "Module objects not found...")
          in
	  Some mp1,(m_info.cur_args@mbids1,mp1,objs), [], []
  in
  (* must be called after get_modtype_substobjs, because of possible
     dependencies on functor arguments *)

  let id = basename (fst oldoname) in
  let mp,resolver = Global.end_module fs id m_info.cur_typ in

  check_subtypes mp m_info.cur_typs;

(* we substitute objects if the module is
   sealed by a signature (ie. mp_from != None *)
  let substobjs = match mp_from,substobjs with
    | None,_ -> substobjs
    | Some mp_from,(mbids,_,objs) ->
	(mbids,mp,subst_objects (map_mp mp_from mp resolver) objs)
  in
  let node = in_module substobjs in
  let objects =
    match keep, m_info.cur_args with
    | [], _ | _, _ :: _ ->
      special@[node]   (* no keep objects or we are defining a functor *)
    | _ ->
      special@[node;in_modkeep keep]   (* otherwise *)
  in
  let newoname = Lib.add_leaves id objects in

  if not (eq_full_path (fst newoname) (fst oldoname)) then
    anomaly (Pp.str "Names generated on start_ and end_module do not match");
  if not (ModPath.equal (mp_of_kn (snd newoname)) mp) then
    anomaly (Pp.str "Kernel and Library names do not match");

  Lib.add_frozen_state () (* to prevent recaching *);
  mp



let module_objects mp =
  let prefix,objects = MPmap.find mp !modtab_objects in
    segment_of_objects prefix objects



(************************************************************************)
(* libraries *)

type library_name = DirPath.t

(* The first two will form substitutive_objects, the last one is keep *)
type library_objects =
    module_path * lib_objects * lib_objects


let register_library dir cenv objs digest =
  let mp = MPfile dir in
  let substobjs, keep, values =
  try
    ignore(Global.lookup_module mp);
    (* if it's in the environment, the cached objects should be correct *)
    Dirmap.find dir !library_cache
  with Not_found ->
    let mp', values = Global.import cenv digest in
    if not (ModPath.equal mp mp') then
      anomaly (Pp.str "Unexpected disk module name");
    let mp,substitute,keep = objs in
    let substobjs = [], mp, substitute in
    let modobjs = substobjs, keep, values in
    library_cache := Dirmap.add dir modobjs !library_cache;
    modobjs
  in
  do_module false "register_library" load_objects 1 dir mp substobjs keep

let get_library_symbols_tbl dir =
  let _,_,values = Dirmap.find dir !library_cache in
  values

let start_library dir =
  let mp = Global.start_library dir in
  openmod_info := { default_module_info with cur_mp = mp };
  Lib.start_compilation dir mp;
  Lib.add_frozen_state ()

let end_library_hook = ref ignore
let set_end_library_hook f = end_library_hook := f

let end_library dir =
  !end_library_hook();
  let prefix, lib_stack = Lib.end_compilation dir in
  let mp,cenv,ast = Global.export dir in
  let substitute, keep, _ = Lib.classify_segment lib_stack in
  cenv,(mp,substitute,keep),ast


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

let in_import =
  declare_object {(default_object "IMPORT MODULE") with
		    cache_function = cache_import;
		    open_function = (fun i o -> if Int.equal i 1 then cache_import o);
		    subst_function = subst_import;
		    classify_function = classify_import }


let import_module export mp =
  Lib.add_anonymous_leaf (in_import (export,mp))

(************************************************************************)
(* module types *)

let start_modtype_ interp_modtype id args mtys fs =
  let mp = Global.start_modtype id in
  let arg_entries = List.concat (List.map (intern_args interp_modtype) args) in
  let sub_mty_l = build_subtypes interp_modtype mp arg_entries mtys in
  let mbids = List.map fst arg_entries in
  openmodtype_info := mbids, sub_mty_l;
  let prefix = Lib.start_modtype id mp fs in
  Nametab.push_dir (Nametab.Until 1) (fst prefix) (DirOpenModtype prefix);
  Lib.add_frozen_state (); mp


let end_modtype () =
  let oldoname,prefix,fs,lib_stack = Lib.end_modtype () in
  let id = basename (fst oldoname) in
  let substitute, _, special = Lib.classify_segment lib_stack in
  let mbids, sub_mty_l = !openmodtype_info in
  let mp = Global.end_modtype fs id in
  let modtypeobjs = mbids, mp, substitute in
  check_subtypes_mt mp sub_mty_l;
  let oname = Lib.add_leaves id (special@[in_modtype (None, modtypeobjs,[])])
  in
  if not (eq_full_path (fst oname) (fst oldoname)) then
    anomaly
      (str "Section paths generated on start_ and end_modtype do not match");
  if not (ModPath.equal (mp_of_kn (snd oname)) mp) then
    anomaly
      (str "Kernel and Library names do not match");

  Lib.add_frozen_state ()(* to prevent recaching *);
  mp


let declare_modtype_ interp_modtype id args mtys (mty,ann) fs =
  let inl = inline_annot ann in
  let mmp = Global.start_modtype id in
  let arg_entries = List.concat (List.map (intern_args interp_modtype) args) in
  let entry = funct_entry arg_entries (interp_modtype (Global.env()) mty) in
  (* NB: check of subtyping will be done in cache_modtype *)
  let sub_mty_l = build_subtypes interp_modtype mmp arg_entries mtys in
  let (mbids,mp_from,objs) = get_modtype_substobjs (Global.env()) inl entry in
  (* Undo the simulated interactive building of the module type *)
  (* and declare the module type as a whole *)

  register_scope_subst ann.ann_scope_subst;
  let subst = map_mp mp_from mmp empty_delta_resolver in
  let substobjs = (mbids,mmp, subst_objects subst objs) in
  reset_scope_subst ();
  Summary.unfreeze_summaries fs;
  ignore (add_leaf id (in_modtype (Some (entry,inl), substobjs, sub_mty_l)));
  mmp


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


let rec get_module_substobjs env inl = function
  | MSEident mp -> MPmap.find mp !modtab_substobjs
  | MSEfunctor (mbid,mty,mexpr) ->
      let (mbids, mp, objs) = get_module_substobjs env inl mexpr in
      (mbid::mbids, mp, objs)
  | MSEapply (fexpr, MSEident mp) as me ->
      let (mbids, mp1, objs),mb_mp1,mp_l =
	get_objs_module_application env me
      in
      let mbids_left,subst =
	compute_subst env mbids mb_mp1.mod_type (List.rev mp_l) inl in
      (mbids_left, mp1,subst_objects subst objs)
  | MSEapply (_,mexpr) -> Modops.error_application_to_not_path mexpr
  | MSEwith (mty, With_Definition _) -> get_module_substobjs env inl mty
  | MSEwith (mty, With_Module (idl,mp)) -> assert false


let declare_module_ interp_modtype interp_modexpr id args res mexpr_o fs =
  let mmp = Global.start_module id in
  let arg_entries = List.concat (List.map (intern_args interp_modtype) args) in

  let funct f m = funct_entry arg_entries (f (Global.env ()) m) in
  let env = Global.env() in
  let mty_entry_o, subs, inl_res = match res with
    | Enforce (mty,ann) ->
        Some (funct interp_modtype mty), [], inline_annot ann
    | Check mtys ->
	None, build_subtypes interp_modtype mmp arg_entries mtys,
        default_inline ()
  in
 
  (*let subs = List.map (Mod_typing.translate_module_type env mmp) mty_sub_l in  *)
  let mexpr_entry_o, inl_expr, scl = match mexpr_o with
    | None -> None, default_inline (), []
    | Some (mexpr,ann) ->
      Some (funct interp_modexpr mexpr), inline_annot ann, ann.ann_scope_subst

  in
  let entry =
    {mod_entry_type = mty_entry_o;
     mod_entry_expr = mexpr_entry_o }
  in

  let substobjs =
    match entry with
      | {mod_entry_type = Some mte} -> get_modtype_substobjs env inl_res mte
      | {mod_entry_expr = Some mexpr} -> get_module_substobjs env inl_expr mexpr
      | _ -> anomaly ~label:"declare_module" (Pp.str "No type, no body ...")
  in
  let (mbids,mp_from,objs) = substobjs in
  (* Undo the simulated interactive building of the module *)
  (* and declare the module as a whole *)
  Summary.unfreeze_summaries fs;
  let mp = mp_of_kn (Lib.make_kn id) in
  let inl = match inl_expr with
  | None -> None
  | _ -> inl_res
  in (* PLTODO *)
  let mp_env,resolver = Global.add_module id entry inl in

  if not (ModPath.equal mp_env mp)
  then anomaly (Pp.str "Kernel and Library names do not match");

  check_subtypes mp subs;
  register_scope_subst scl;
  let subst = map_mp mp_from mp_env resolver in
  let substobjs = (mbids,mp_env, subst_objects subst objs) in
  reset_scope_subst ();
  ignore (add_leaf id (in_module substobjs));
  mmp

(* Include *)

let do_include_objs i do_load do_open ((sp,kn),objs) =
  let dir = Libnames.dirpath sp in
  let mp = KerName.modpath kn in
  let prefix = (dir,(mp,DirPath.empty)) in
  if do_load then load_objects i prefix objs;
  if do_open then open_objects i prefix objs

let cache_include oname_objs = do_include_objs 1 true true oname_objs
let load_include i oname_objs = do_include_objs i true false oname_objs
let open_include i oname_objs = do_include_objs i false true oname_objs

let subst_include (subst,objs) = subst_objects subst objs

let classify_include objs = Substitute objs

type include_obj = Lib.lib_objects

let (in_include : include_obj -> obj),
    (out_include : obj -> include_obj) =
  declare_object_full {(default_object "INCLUDE") with
    cache_function = cache_include;
    load_function = load_include;
    open_function = open_include;
    subst_function = subst_include;
    classify_function = classify_include }

let rec include_subst env mp reso mbids sign inline =
  match mbids with
    | [] -> empty_subst
    | mbid::mbids ->
	let farg_id, farg_b, fbody_b = Modops.destr_functor env sign in
	let subst = include_subst env mp reso mbids fbody_b inline in
	let mp_delta =
	  Modops.inline_delta_resolver env inline mp farg_id farg_b reso
	in
	join (map_mbid mbid mp mp_delta) subst

exception NothingToDo

let get_includeself_substobjs env mp1 mbids objs me is_mod inline =
  try
    let mb_mp = match me with
      | MSEident mp ->
	  if is_mod then
	    Environ.lookup_module mp env
	  else
	    Modops.module_body_of_type mp (Environ.lookup_modtype mp env)
      | MSEapply(fexpr, MSEident p) as mexpr ->
	  let _,mb_mp,mp_l =
	    if is_mod then
	      get_objs_module_application env mexpr
	    else
	      let o,mtb_mp,mp_l = get_objs_modtype_application env mexpr in
	      o,Modops.module_body_of_type mtb_mp.typ_mp mtb_mp,mp_l
	  in
	  List.fold_left
	    (fun mb _ ->
	       match mb.mod_type with
		 |  SEBfunctor(_,_,str) -> {mb with mod_type = str}
		 | _ -> error "Application of a functor with too much arguments.")
	    mb_mp mp_l
      | _ -> raise NothingToDo
    in
    let reso = fst (Safe_typing.delta_of_senv (Global.safe_env ())) in
    let subst = include_subst env mp1 reso mbids mb_mp.mod_type inline in
    subst_objects subst objs
  with NothingToDo -> objs




let declare_one_include_inner annot (me,is_mod) =
  let env = Global.env() in
  let cur_mp = fst (current_prefix ()) in
  let inl = inline_annot annot in
  let (mbids,mp,objs)=
    if is_mod then
      get_module_substobjs env inl me
    else
      get_modtype_substobjs env inl me in
  let objs =
    if List.is_empty mbids then objs
    else get_includeself_substobjs env cur_mp mbids objs me is_mod inl
  in
  let id = current_mod_id() in
  let resolver = Global.add_include me is_mod inl in
  register_scope_subst annot.ann_scope_subst;
  let subst = map_mp mp cur_mp resolver in
  let substobjs = subst_objects subst objs in
  reset_scope_subst ();
  ignore (add_leaf id (in_include substobjs))

let declare_one_include interp_struct (me_ast,annot) =
  declare_one_include_inner annot
    (interp_struct (Global.env()) me_ast)

let declare_include_ interp_struct me_asts =
  List.iter (declare_one_include interp_struct) me_asts

(** Versions of earlier functions taking care of the freeze/unfreeze
    of summaries *)

let protect_summaries f =
  let fs = Summary.freeze_summaries ~marshallable:false in
  try f fs
  with reraise ->
    (* Something wrong: undo the whole process *)
    let reraise = Errors.push reraise in
    let () = Summary.unfreeze_summaries fs in
    raise reraise

let declare_include interp_struct me_asts =
  protect_summaries
    (fun _ -> declare_include_ interp_struct me_asts)

let declare_modtype interp_mt interp_mix id args mtys mty_l =
  let declare_mt fs = match mty_l with
    | [] -> assert false
    | [mty] -> declare_modtype_ interp_mt id args mtys mty fs
    | mty_l ->
	ignore (start_modtype_ interp_mt id args mtys fs);
	declare_include_ interp_mix mty_l;
	end_modtype ()
  in
  protect_summaries declare_mt

let start_modtype interp_modtype id args mtys =
  protect_summaries (start_modtype_ interp_modtype id args mtys)

let declare_module interp_mt interp_me interp_mix id args mtys me_l =
  let declare_me fs = match me_l with
    | [] -> declare_module_ interp_mt interp_me id args mtys None fs
    | [me] -> declare_module_ interp_mt interp_me id args mtys (Some me) fs
    | me_l ->
	ignore (start_module_ interp_mt None id args mtys fs);
	declare_include_ interp_mix me_l;
	end_module ()
  in
  protect_summaries declare_me

let start_module interp_modtype export id args res =
 protect_summaries (start_module_ interp_modtype export id args res)


(*s Iterators. *)

let iter_all_segments f =
  let _ =
    MPmap.iter
      (fun _ (prefix,objects) ->
	 let rec apply_obj (id,obj) = match object_tag obj with
	   | "INCLUDE" -> List.iter apply_obj (out_include obj)
	   | _ -> f (make_oname prefix id) obj
         in
	 List.iter apply_obj objects)
      !modtab_objects
  in
  let apply_node = function
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
