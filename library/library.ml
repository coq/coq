(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util

open Names
open Libnames
open Nameops
open Safe_typing
open Libobject
open Lib
open Nametab
open Declaremods

(*************************************************************************)
(*s Load path. Mapping from physical to logical paths etc.*)

type logical_path = dir_path

let load_path = ref ([],[] : System.physical_path list * logical_path list)

let get_load_path () = fst !load_path


let find_logical_path phys_dir = 
  let phys_dir = System.canonical_path_name phys_dir in
  match list_filter2 (fun p d -> p = phys_dir) !load_path with
  | _,[dir] -> dir
  | _,[] -> Nameops.default_root_prefix
  | _,l -> anomaly ("Two logical paths are associated to "^phys_dir)

let is_in_load_paths phys_dir =
  let dir = System.canonical_path_name phys_dir in
  let lp = get_load_path () in
  let check_p = fun p -> (String.compare dir p) == 0 in
  List.exists check_p lp

let remove_path dir =
  let dir = System.canonical_path_name dir in
  load_path := list_filter2 (fun p d -> p <> dir) !load_path

let add_load_path_entry (phys_path,coq_path) =
  let phys_path = System.canonical_path_name phys_path in
  match list_filter2 (fun p d -> p = phys_path) !load_path with
  | _,[dir] ->
      if coq_path <> dir 
        (* If this is not the default -I . to coqtop *)
        && not
        (phys_path = System.canonical_path_name Filename.current_dir_name
         && coq_path = Nameops.default_root_prefix)
      then
	begin
          (* Assume the user is concerned by library naming *)
	  if dir <> Nameops.default_root_prefix then
	    (Options.if_verbose warning (phys_path^" was previously bound to "
	    ^(string_of_dirpath dir)
	    ^("\nIt is remapped to "^(string_of_dirpath coq_path)));
             flush_all ());
	  remove_path phys_path;
	  load_path := (phys_path::fst !load_path, coq_path::snd !load_path)
	end
  | _,[] ->
      load_path := (phys_path :: fst !load_path, coq_path :: snd !load_path)
  | _ -> anomaly ("Two logical paths are associated to "^phys_path)

let physical_paths (dp,lp) = dp

let load_path_of_logical_path dir =
  fst (list_filter2 (fun p d -> d = dir) !load_path)

let get_full_load_path () = List.combine (fst !load_path) (snd !load_path)

(************************************************************************)
(*s Modules on disk contain the following informations (after the magic 
    number, and before the digest). *)

type compilation_unit_name = dir_path

type library_disk = { 
  md_name : compilation_unit_name;
  md_compiled : compiled_library;
  md_objects : library_objects;
  md_deps : (compilation_unit_name * Digest.t) list;
  md_imports : compilation_unit_name list }

(*s Modules loaded in memory contain the following informations. They are
    kept in the global table [libraries_table]. *)

type library_t = {
  library_name : compilation_unit_name;
  library_filename : System.physical_path;
  library_compiled : compiled_library;
  library_objects : library_objects;
  library_deps : (compilation_unit_name * Digest.t) list;
  library_imports : compilation_unit_name list;
  library_digest : Digest.t }

module CompilingLibraryOrdered = 
  struct
    type t = dir_path
    let compare d1 d2 =
      Pervasives.compare
        (List.rev (repr_dirpath d1)) (List.rev (repr_dirpath d2))
  end

module CompilingLibraryMap = Map.Make(CompilingLibraryOrdered)

(* This is a map from names to libraries *)
let libraries_table = ref CompilingLibraryMap.empty

(* These are the _ordered_ lists of loaded, imported and exported libraries *)
let libraries_loaded_list = ref []
let libraries_imports_list = ref []
let libraries_exports_list = ref []

let freeze () =
  !libraries_table,
  !libraries_loaded_list,
  !libraries_imports_list,
  !libraries_exports_list

let unfreeze (mt,mo,mi,me) = 
  libraries_table := mt;
  libraries_loaded_list := mo;
  libraries_imports_list := mi;
  libraries_exports_list := me

let init () =
  libraries_table := CompilingLibraryMap.empty;
  libraries_loaded_list := [];
  libraries_imports_list := [];
  libraries_exports_list := []

let _ = 
  Summary.declare_summary "MODULES"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_module = false;
      Summary.survive_section = false }

let find_library s =
  CompilingLibraryMap.find s !libraries_table

let try_find_library s =
  try find_library s
  with Not_found ->
    error ("Unknown library " ^ (string_of_dirpath s))

let library_full_filename m = (find_library m).library_filename

let library_is_loaded dir =
  try let _ = CompilingLibraryMap.find dir !libraries_table in true
  with Not_found -> false

let library_is_opened dir = 
  List.exists (fun m -> m.library_name = dir) !libraries_imports_list

let library_is_exported dir =
  List.exists (fun m -> m.library_name = dir) !libraries_exports_list

let loaded_libraries () = 
  List.map (fun m -> m.library_name) !libraries_loaded_list

let opened_libraries () =
  List.map (fun m -> m.library_name) !libraries_imports_list

  (* If a library is loaded several time, then the first occurrence must
     be performed first, thus the libraries_loaded_list ... *)

let register_loaded_library m =
  let rec aux = function
    | [] -> [m]
    | m'::_ as l when m'.library_name = m.library_name -> l
    | m'::l' -> m' :: aux l' in
  libraries_loaded_list := aux !libraries_loaded_list;
  libraries_table := CompilingLibraryMap.add m.library_name m !libraries_table

  (* ... while if a library is imported/exported several time, then
     only the last occurrence is really needed - though the imported
     list may differ from the exported list (consider the sequence
     Export A; Export B; Import A which results in A;B for exports but
     in B;A for imports) *)

let rec remember_last_of_each l m =
  match l with
  | [] -> [m]
  | m'::l' when m'.library_name = m.library_name -> remember_last_of_each l' m
  | m'::l' -> m' :: remember_last_of_each l' m

let register_open_library export m =
  libraries_imports_list := remember_last_of_each !libraries_imports_list m;
  if export then 
    libraries_exports_list := remember_last_of_each !libraries_exports_list m

(************************************************************************)
(*s Opening libraries *)

(*s [open_library s] opens a library. The library [s] and all
  libraries needed by [s] are assumed to be already loaded. When
  opening [s] we recursively open all the libraries needed by [s]
  and tagged [exported]. *)

let eq_lib_name m1 m2 = m1.library_name = m2.library_name

let open_library export explicit_libs m =
  if
    (* Only libraries indirectly to open are not reopen *)
    (* Libraries explicitly mentionned by the user are always reopen *)
    List.exists (eq_lib_name m) explicit_libs
    or not (library_is_opened m.library_name)
  then begin
    register_open_library export m;
    Declaremods.really_import_module (MPfile m.library_name)
  end
  else
    if export then 
      libraries_exports_list := remember_last_of_each !libraries_exports_list m

let open_libraries export modl = 
  let to_open_list = 
    List.fold_left
      (fun l m ->
         let subimport =
           List.fold_left
             (fun l m -> remember_last_of_each l (try_find_library m))
             l m.library_imports
         in remember_last_of_each subimport m)
      [] modl in
  List.iter (open_library export modl) to_open_list


(**********************************************************************)
(* import and export  -  synchronous operations*)

let cache_import (_,(dir,export)) = 
  open_libraries export [try_find_library dir]

let open_import i (_,(dir,_) as obj) =
  if i=1 then
    (* even if the library is already imported, we re-import it *)
    (* if not (library_is_opened dir) then *)
      cache_import obj

let subst_import (_,_,o) = o

let export_import o = Some o

let classify_import (_,(_,export as obj)) = 
  if export then Substitute obj else Dispose


let (in_import, out_import) =
  declare_object {(default_object "IMPORT LIBRARY") with 
       cache_function = cache_import;
       open_function = open_import;
       subst_function = subst_import;
       classify_function = classify_import }


(************************************************************************)
(*s Loading from disk to cache (preparation phase) *)

let vo_magic_number7 = 07993 (* V8.0pl3 final old syntax *)
let vo_magic_number8 = 08003 (* V8.0pl3 final new syntax *)

let (raw_extern_library7, raw_intern_library7) =
  System.raw_extern_intern vo_magic_number7 ".vo"

let (raw_extern_library8, raw_intern_library8) =
  System.raw_extern_intern vo_magic_number8 ".vo"

let raw_intern_library a =
  if !Options.v7 then
    try raw_intern_library7 a
    with System.Bad_magic_number fname ->
      let _= raw_intern_library8 a in
      error "Inconsistent compiled files: you probably want to use Coq in new syntax and remove the option -v7 or -translate"
  else
    try raw_intern_library8 a
    with System.Bad_magic_number fname ->
      let _= raw_intern_library7 a in
      error "Inconsistent compiled files: you probably want to use Coq in old syntax by setting options -v7 or -translate"

let raw_extern_library =
  if !Options.v7 then raw_extern_library7 else raw_extern_library8

(* cache for loaded libraries *)
let compunit_cache = ref CompilingLibraryMap.empty

let _ = 
  Summary.declare_summary "MODULES-CACHE"
    { Summary.freeze_function = (fun () -> !compunit_cache);
      Summary.unfreeze_function = (fun cu -> compunit_cache := cu);
      Summary.init_function = 
	(fun () -> compunit_cache := CompilingLibraryMap.empty);
      Summary.survive_module = true;
      Summary.survive_section = true }

(*s [load_library s] loads the library [s] from the disk, and [find_library s]
   returns the library of name [s], loading it if necessary. 
   The boolean [doexp] specifies if we open the libraries which are declared
   exported in the dependencies (it is [true] at the highest level;
   then same value as for caller is reused in recursive loadings). *)

exception LibUnmappedDir
exception LibNotFound
type library_location = LibLoaded | LibInPath

let locate_absolute_library dir =
  (* Look if loaded in current environment *)
  try
    let m = CompilingLibraryMap.find dir !libraries_table in
    (dir, m.library_filename)
  with Not_found ->
  (* Look if in loadpath *)
  try
    let pref, base = split_dirpath dir in
    let loadpath = load_path_of_logical_path pref in
    if loadpath = [] then raise LibUnmappedDir;
    let name = (string_of_id base)^".vo" in
    let _, file = System.where_in_path loadpath name in
    (dir, file)
  with Not_found ->  raise LibNotFound

let with_magic_number_check f a =
  try f a
  with System.Bad_magic_number fname ->
    errorlabstrm "with_magic_number_check"
    (str"file " ++ str fname ++ spc () ++ str"has bad magic number." ++
    spc () ++ str"It is corrupted" ++ spc () ++
    str"or was compiled with another version of Coq.")

let lighten_library m = 
  if !Options.dont_load_proofs then lighten_library m else m

let mk_library md f digest = {
  library_name = md.md_name;
  library_filename = f;
  library_compiled = lighten_library md.md_compiled;
  library_objects = md.md_objects;
  library_deps = md.md_deps;
  library_imports = md.md_imports;
  library_digest = digest }

let intern_from_file f =
  let ch = with_magic_number_check raw_intern_library f in
  let md = System.marshal_in ch in
  let digest = System.marshal_in ch in
  close_in ch;
  mk_library md f digest

let rec intern_library (dir, f) =
  try
    (* Look if in the current logical environment *)
    CompilingLibraryMap.find dir !libraries_table
  with Not_found ->
  try
    (* Look if already loaded in cache and consequently its dependencies *)
    CompilingLibraryMap.find dir !compunit_cache
  with Not_found ->
    (* [dir] is an absolute name which matches [f] which must be in loadpath *)
    let m = intern_from_file f in
    if dir <> m.library_name then
      errorlabstrm "load_physical_library"
	(str ("The file " ^ f ^ " contains library") ++ spc () ++
	 pr_dirpath m.library_name ++ spc () ++ str "and not library" ++
         spc() ++ pr_dirpath dir);
    intern_and_cache_library dir m

and intern_and_cache_library dir m =
  compunit_cache := CompilingLibraryMap.add dir m !compunit_cache;
  try
    List.iter (intern_mandatory_library dir) m.library_deps;
    m
  with e ->
    compunit_cache := CompilingLibraryMap.remove dir !compunit_cache; 
    raise e

and intern_mandatory_library caller (dir,d) =
  let m = intern_absolute_library_from dir in
  if d <> m.library_digest then
    error ("compiled library "^(string_of_dirpath caller)^
	   " makes inconsistent assumptions over library "
	   ^(string_of_dirpath dir))

and intern_absolute_library_from dir =
  try
    intern_library (locate_absolute_library dir)
  with
  | LibUnmappedDir ->
      let prefix, dir = fst (split_dirpath dir), string_of_dirpath dir in
      errorlabstrm "load_absolute_library_from"
      (str ("Cannot load "^dir^":") ++ spc () ++ 
      str "no physical path bound to" ++ spc () ++ pr_dirpath prefix ++ fnl ())
  | LibNotFound ->
      errorlabstrm "load_absolute_library_from"
      (str"Cannot find library " ++ pr_dirpath dir ++ str" in loadpath")
  | e -> raise e

let rec_intern_library mref = let _ = intern_library mref in ()

let check_library_short_name f dir = function
  | Some id when id <> snd (split_dirpath dir) ->
      errorlabstrm "check_library_short_name"
      (str ("The file " ^ f ^ " contains library") ++ spc () ++
      pr_dirpath dir ++ spc () ++ str "and not library" ++ spc () ++
      pr_id id)
  | _ -> ()

let rec_intern_by_filename_only id f =
  let m = intern_from_file f in
  (* Only the base name is expected to match *)
  check_library_short_name f m.library_name id;
  (* We check no other file containing same library is loaded *)
  try
    let m' = CompilingLibraryMap.find m.library_name !libraries_table in
    Options.if_verbose warning 
      ((string_of_dirpath m.library_name)^" is already loaded from file "^
       m'.library_filename);
    m.library_name
  with Not_found ->
    let m = intern_and_cache_library m.library_name m in
    m.library_name

let locate_qualified_library qid =
  try
    (* Search library in loadpath *)
    let dir, base = repr_qualid qid in 
    let loadpath =
      if repr_dirpath dir = [] then get_load_path ()
      else 
        (* we assume dir is an absolute dirpath *)
	load_path_of_logical_path dir
    in
    if loadpath = [] then raise LibUnmappedDir;
    let name =  (string_of_id base)^".vo" in
    let path, file = System.where_in_path loadpath name in
    let dir = extend_dirpath (find_logical_path path) base in
    (* Look if loaded *)
    try 
      (LibLoaded, dir, library_full_filename dir)      
    with Not_found ->
      (LibInPath, dir, file)
  with Not_found -> raise LibNotFound

let rec_intern_qualified_library (loc,qid) =
  try
    let (_,dir,f) = locate_qualified_library qid in
    rec_intern_library (dir,f);
    dir
  with
  | LibUnmappedDir ->
      let prefix, id = repr_qualid qid in
      user_err_loc (loc, "rec_intern_qualified_library",
        str ("Cannot load "^(string_of_id id)^":") ++ spc () ++ 
        str "no physical path bound to" ++ spc () ++ pr_dirpath prefix ++
        fnl ())
  | LibNotFound ->
      user_err_loc (loc, "rec_intern_qualified_library",
        str"Cannot find library " ++ pr_qualid qid ++ str" in loadpath")

let rec_intern_library_from_file idopt f =
  (* A name is specified, we have to check it contains library id *)
  let _, f = System.find_file_in_path (get_load_path ()) (f^".vo") in
  rec_intern_by_filename_only idopt f

(**********************************************************************)
(*s [require_library] loads and opens a library. This is a synchronized
    operation. It is performed as follows:

  preparation phase: (functions require_library* ) the library and its 
    dependencies are read from to disk to the compunit_cache 
    (using intern_* )

  execution phase: (through add_leaf and cache_require)
    the library is loaded in the environment and Nametab, the objects are 
    registered etc, using functions from Declaremods (via load_library, 
    which recursively loads its dependencies)


  The [read_library] operation is very similar, but does not "open"
    the library
*)

type library_reference = dir_path list * bool option

let string_of_library (_,dir,_) = string_of_id (List.hd (repr_dirpath dir))

let rec load_library dir =
  try
    (* Look if loaded in current env (and consequently its dependencies) *)
    CompilingLibraryMap.find dir !libraries_table
  with Not_found ->
    (* [dir] is an absolute name matching [f] which must be in loadpath *)
    let m =
      try CompilingLibraryMap.find dir !compunit_cache
      with Not_found ->
        anomaly ((string_of_dirpath dir)^" should be in cache")
    in
    List.iter (fun (dir,_) -> ignore (load_library dir)) m.library_deps;
    Declaremods.register_library
      m.library_name 
      m.library_compiled 
      m.library_objects 
      m.library_digest;
    register_loaded_library m;
    m

let cache_require (_,(modl,export)) =
  let ml = list_map_left load_library modl in
  match export with
    | None -> ()
    | Some export -> open_libraries export ml

let load_require  _ (_,(modl,_)) =
  ignore(list_map_left load_library modl)

  (* keeps the require marker for closed section replay but removes
     OS dependent fields from .vo files for cross-platform compatibility *)
let export_require (l,e) = Some (l,e)

let (in_require, out_require) =
  declare_object {(default_object "REQUIRE") with
       cache_function = cache_require;
       load_function = load_require;
       export_function = export_require;
       classify_function = (fun (_,o) -> Anticipate o) }

let xml_require = ref (fun d -> ())
let set_xml_require f = xml_require := f

let require_library spec qidl export =
(*
  if sections_are_opened () && Options.verbose () then
    warning ("Objets of "^(string_of_library modref)^
             " not surviving sections (e.g. Grammar \nand Hints)\n"^
             "will be removed at the end of the section");
*)
  let modrefl = List.map rec_intern_qualified_library qidl in
    if Lib.is_modtype () || Lib.is_module () then begin
      add_anonymous_leaf (in_require (modrefl,None));
      List.iter
	(fun dir ->
	   add_anonymous_leaf (in_import (dir, export)))
	modrefl
    end
    else
      add_anonymous_leaf (in_require (modrefl,Some export));
  if !Options.xml_export then List.iter !xml_require modrefl;
  add_frozen_state ()

let require_library_from_file spec idopt file export =
  let modref = rec_intern_library_from_file idopt file in
    if Lib.is_modtype () || Lib.is_module () then begin
      add_anonymous_leaf (in_require ([modref],None));
      add_anonymous_leaf (in_import (modref, export))
    end
    else
      add_anonymous_leaf (in_require ([modref],Some export));
    if !Options.xml_export then !xml_require modref;
    add_frozen_state ()


(* read = require without opening *)

let read_library qid =
  let modref = rec_intern_qualified_library qid in
  add_anonymous_leaf (in_require ([modref],None));
  if !Options.xml_export then !xml_require modref;
  add_frozen_state ()

let read_library_from_file f =
  let _, f = System.find_file_in_path (get_load_path ()) (f^".vo") in
  let modref = rec_intern_by_filename_only None f in
  add_anonymous_leaf (in_require ([modref],None));
  if !Options.xml_export then !xml_require modref;
  add_frozen_state ()


(* called at end of section *)

let reload_library modrefl =
  add_anonymous_leaf (in_require modrefl);
  add_frozen_state ()



(* the function called by Vernacentries.vernac_import *)

let import_library export (loc,qid) =
  try
    match Nametab.locate_module qid with
	MPfile dir -> 
	  if Lib.is_modtype () || Lib.is_module () || not export then
	    add_anonymous_leaf (in_import (dir, export))
	  else
	    add_anonymous_leaf (in_require ([dir], Some export))
      | mp ->
	  import_module export mp
  with
      Not_found ->
	user_err_loc
        (loc,"import_library",
	 str ((string_of_qualid qid)^" is not a module"))
  
(************************************************************************)
(*s [save_library s] saves the library [m] to the disk. *)

let start_library f = 
  let _,longf = 
    System.find_file_in_path (get_load_path ()) (f^".v") in
  let ldir0 = find_logical_path (Filename.dirname longf) in
  let id = id_of_string (Filename.basename f) in
  let ldir = extend_dirpath ldir0 id in
  Declaremods.start_library ldir;
  ldir,longf

let current_deps () =
  List.map (fun m -> (m.library_name, m.library_digest)) !libraries_loaded_list

let current_reexports () =
  List.map (fun m -> m.library_name) !libraries_exports_list

let save_library_to s f =
  let cenv, seg = Declaremods.end_library s in
  let md = { 
    md_name = s;
    md_compiled = cenv;
    md_objects = seg;
    md_deps = current_deps ();
    md_imports = current_reexports () } in
  let (f',ch) = raw_extern_library f in
  try
    System.marshal_out ch md;
    flush ch;
    let di = Digest.file f' in
    System.marshal_out ch di;
    close_out ch
  with e -> (warning ("Removed file "^f');close_out ch; Sys.remove f'; raise e)

(*s Pretty-printing of libraries state. *)
 
(* this function is not used... *)
let fmt_libraries_state () =
  let opened = opened_libraries ()
  and loaded = loaded_libraries () in
  (str "Imported (open) Modules: " ++
     prlist_with_sep pr_spc pr_dirpath opened ++ fnl () ++
     str "Loaded Modules: " ++
     prlist_with_sep pr_spc pr_dirpath loaded ++ fnl ())


(*s For tactics/commands requiring vernacular libraries *)

let check_required_library d =
  let d' = List.map id_of_string d in
  let dir = make_dirpath (List.rev d') in
  if not (library_is_loaded dir) then
(* Loading silently ...
    let m, prefix = list_sep_last d' in
    read_library 
     (dummy_loc,make_qualid (make_dirpath (List.rev prefix)) m)
*)
(* or failing ...*)
    error ("Library "^(list_last d)^" has to be required first")


(*s Display the memory use of a library. *)

open Printf

let mem s =
  let m = try_find_library s in
  h 0 (str (sprintf "%dk (cenv = %dk / seg = %dk)"
		 (size_kb m) (size_kb m.library_compiled) 
		 (size_kb m.library_objects)))
