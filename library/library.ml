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

let load_paths = ref ([],[] : System.physical_path list * logical_path list)

let get_load_paths () = fst !load_paths

(* Hints to partially detects if two paths refer to the same repertory *)
let rec remove_path_dot p = 
  let curdir = Filename.concat Filename.current_dir_name "" in (* Unix: "./" *)
  let n = String.length curdir in
  if String.length p > n && String.sub p 0 n = curdir then
    remove_path_dot (String.sub p n (String.length p - n))
  else
    p

let strip_path p =
  let cwd = Filename.concat (Sys.getcwd ()) "" in (* Unix: "`pwd`/" *)
  let n = String.length cwd in
  if String.length p > n && String.sub p 0 n = cwd then
    remove_path_dot (String.sub p n (String.length p - n))
  else
    remove_path_dot p

let canonical_path_name p =
  let current = Sys.getcwd () in
  try 
    Sys.chdir p;
    let p' = Sys.getcwd () in
    Sys.chdir current;
    p'
  with Sys_error _ ->
    (* We give up to find a canonical name and just simplify it... *)
    strip_path p

let find_logical_path phys_dir = 
  let phys_dir = canonical_path_name phys_dir in
  match list_filter2 (fun p d -> p = phys_dir) !load_paths with
  | _,[dir] -> dir
  | _,[] -> Nameops.default_root_prefix
  | _,l -> anomaly ("Two logical paths are associated to "^phys_dir)

let is_in_load_paths phys_dir =
  let dir = canonical_path_name phys_dir in
  let lp = get_load_paths () in
  let check_p = fun p -> (String.compare dir p) == 0 in
    List.exists check_p lp 

let remove_load_path dir =
  load_paths := list_filter2 (fun p d -> p <> dir) !load_paths

let add_load_path (phys_path,coq_path) =
  let phys_path = canonical_path_name phys_path in
    match list_filter2 (fun p d -> p = phys_path) !load_paths with
      | _,[dir] ->
	  if coq_path <> dir 
            (* If this is not the default -I . to coqtop *)
            && not
            (phys_path = canonical_path_name Filename.current_dir_name
		&& coq_path = Nameops.default_root_prefix)
	  then
	    begin
              (* Assume the user is concerned by library naming *)
	      if dir <> Nameops.default_root_prefix then
		(Options.if_verbose warning (phys_path^" was previously bound to "
					     ^(string_of_dirpath dir)
					     ^("\nIt is remapped to "^(string_of_dirpath coq_path)));
		 flush_all ());
	      remove_load_path phys_path;
	      load_paths := (phys_path::fst !load_paths, coq_path::snd !load_paths)
	    end
      | _,[] ->
	  load_paths := (phys_path :: fst !load_paths, coq_path :: snd !load_paths)
      | _ -> anomaly ("Two logical paths are associated to "^phys_path)

let physical_paths (dp,lp) = dp

let load_paths_of_dir_path dir =
  fst (list_filter2 (fun p d -> d = dir) !load_paths)
    
let get_full_load_paths () = List.combine (fst !load_paths) (snd !load_paths)

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

module LibraryOrdered = 
  struct
    type t = dir_path
    let compare d1 d2 =
      Pervasives.compare
        (List.rev (repr_dirpath d1)) (List.rev (repr_dirpath d2))
  end

module LibraryMap = Map.Make(LibraryOrdered)

(* This is a map from names to loaded libraries *)
let libraries_table = ref LibraryMap.empty

(* These are the _ordered_ sets of loaded, imported and exported libraries *)
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
  libraries_table := LibraryMap.empty;
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

(* various requests to the tables *)

let find_library dir =
  LibraryMap.find dir !libraries_table

let try_find_library dir =
  try find_library dir
  with Not_found ->
    error ("Unknown library " ^ (string_of_dirpath dir))

let library_full_filename dir = (find_library dir).library_filename

let library_is_loaded dir =
  try let _ = find_library dir in true
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
  libraries_table := LibraryMap.add m.library_name m !libraries_table

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

(* [open_library export explicit m] opens library [m] if not already
   opened _or_ if explicitly asked to be (re)opened *)

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

(* open_libraries recursively open a list of libraries but opens only once 
   a library that is re-exported many times *)

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
(*s Low-level interning/externing of libraries to files *)

(*s Loading from disk to cache (preparation phase) *)

let vo_magic_number = 08099 (* V8.1 beta *)

let (raw_extern_library, raw_intern_library) =
  System.raw_extern_intern vo_magic_number ".vo"

let with_magic_number_check f a =
  try f a
  with System.Bad_magic_number fname ->
    errorlabstrm "with_magic_number_check"
    (str"file " ++ str fname ++ spc () ++ str"has bad magic number." ++
    spc () ++ str"It is corrupted" ++ spc () ++
    str"or was compiled with another version of Coq.")

(************************************************************************)
(*s Locate absolute or partially qualified library names in the path *)

exception LibUnmappedDir
exception LibNotFound
type library_location = LibLoaded | LibInPath

let locate_absolute_library dir =
  (* Search in loadpath *)
  let pref, base = split_dirpath dir in
  let loadpath = load_paths_of_dir_path pref in
  if loadpath = [] then raise LibUnmappedDir;
  try
    let name = (string_of_id base)^".vo" in
    let _, file = System.where_in_path loadpath name in
    (dir, file)
  with Not_found ->
  (* Last chance, removed from the file system but still in memory *)
  try
    (dir, library_full_filename dir)
  with Not_found ->
    raise LibNotFound

let locate_qualified_library qid =
  try
    (* Search library in loadpath *)
    let dir, base = repr_qualid qid in 
    let loadpath =
      if repr_dirpath dir = [] then get_load_paths ()
      else 
        (* we assume dir is an absolute dirpath *)
	load_paths_of_dir_path dir
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

let explain_locate_library_error qid = function
  | LibUnmappedDir ->
      let prefix, _ = repr_qualid qid in
      errorlabstrm "load_absolute_library_from"
      (str "Cannot load " ++ pr_qualid qid ++ str ":" ++ spc () ++ 
      str "no physical path bound to" ++ spc () ++ pr_dirpath prefix ++ fnl ())
  | LibNotFound ->
      errorlabstrm "load_absolute_library_from"
      (str"Cannot find library " ++ pr_qualid qid ++ str" in loadpath")
  | e -> raise e

let try_locate_absolute_library dir =
  try
    locate_absolute_library dir
  with e ->
    explain_locate_library_error (qualid_of_dirpath dir) e

let try_locate_qualified_library (loc,qid) =
  try
    let (_,dir,f) = locate_qualified_library qid in
    dir,f
  with e -> 
    explain_locate_library_error qid e


(************************************************************************)
(* Internalise libraries *)

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

let rec intern_library needed (dir, f) =
  (* Look if in the current logical environment *)
  try find_library dir, needed
  with Not_found ->
  (* Look if already listed and consequently its dependencies too *)
  try List.assoc dir needed, needed
  with Not_found ->
  (* [dir] is an absolute name which matches [f] which must be in loadpath *)
  let m = intern_from_file f in
  if dir <> m.library_name then
    errorlabstrm "load_physical_library"
      (str ("The file " ^ f ^ " contains library") ++ spc () ++
       pr_dirpath m.library_name ++ spc () ++ str "and not library" ++
       spc() ++ pr_dirpath dir);
  m, intern_library_deps needed dir m

and intern_library_deps needed dir m =
  (dir,m)::List.fold_left (intern_mandatory_library dir) needed m.library_deps

and intern_mandatory_library caller needed (dir,d) =
  let m,needed = intern_library needed (try_locate_absolute_library dir) in
  if d <> m.library_digest then
    error ("compiled library "^(string_of_dirpath caller)^
	   " makes inconsistent assumptions over library "
	   ^(string_of_dirpath dir));
  needed

let rec_intern_library needed mref =
  let _,needed = intern_library needed mref in needed

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
    let m' = find_library m.library_name in
    Options.if_verbose warning 
      ((string_of_dirpath m.library_name)^" is already loaded from file "^
       m'.library_filename);
    m.library_name, []
  with Not_found ->
    let needed = intern_library_deps [] m.library_name m in
    m.library_name, needed

let rec_intern_library_from_file idopt f =
  (* A name is specified, we have to check it contains library id *)
  let _, f = System.find_file_in_path (get_load_paths ()) (f^".vo") in
  rec_intern_by_filename_only idopt f

(**********************************************************************)
(*s [require_library] loads and opens a library. This is a synchronized
    operation. It is performed as follows:

  preparation phase: (functions require_library* ) the library and its 
    dependencies are read from to disk (using intern_* )
    [they are read from disk to ensure that at section/module
     discharging time, the physical library referred to outside the
     section/module is the one that was used at type-checking time in
     the section/module]

  execution phase: (through add_leaf and cache_require)
    the library is loaded in the environment and Nametab, the objects are 
    registered etc, using functions from Declaremods (via load_library, 
    which recursively loads its dependencies)


  The [read_library] operation is very similar, but does not "open"
    the library
*)

type library_reference = dir_path list * bool option

let register_library (dir,m) =
  Declaremods.register_library
    m.library_name 
    m.library_compiled 
    m.library_objects 
    m.library_digest;
  register_loaded_library m

  (* [needed] is the ordered list of libraries not already loaded *)
let cache_require (_,(needed,modl,export)) =
  List.iter register_library needed;
  option_iter (fun exp -> open_libraries exp (List.map find_library modl))
    export

let load_require  _ (_,(needed,modl,_)) =
  List.iter register_library needed

  (* keeps the require marker for closed section replay but removes
     OS dependent fields from .vo files for cross-platform compatibility *)
let export_require (_,l,e) = Some ([],l,e)

let discharge_require (_,o) = Some o

let (in_require, out_require) =
  declare_object {(default_object "REQUIRE") with
       cache_function = cache_require;
       load_function = load_require;
       export_function = export_require;
       discharge_function = discharge_require;
       classify_function = (fun (_,o) -> Anticipate o) }

(* Require libraries, import them if [export <> None], mark them for export
   if [export = Some true] *)

(* read = require without opening *)

let xml_require = ref (fun d -> ())
let set_xml_require f = xml_require := f

let require_library qidl export =
  let modrefl = List.map try_locate_qualified_library qidl in
  let needed = List.rev (List.fold_left rec_intern_library [] modrefl) in
  let modrefl = List.map fst modrefl in
    if Lib.is_modtype () || Lib.is_module () then begin
      add_anonymous_leaf (in_require (needed,modrefl,None));
      option_iter (fun exp ->
	List.iter (fun dir -> add_anonymous_leaf (in_import(dir,exp))) modrefl)
	export
    end
    else
      add_anonymous_leaf (in_require (needed,modrefl,export));
  if !Options.xml_export then List.iter !xml_require modrefl;
  add_frozen_state ()

let require_library_from_file idopt file export =
  let modref,needed = rec_intern_library_from_file idopt file in
  let needed = List.rev needed in
  if Lib.is_modtype () || Lib.is_module () then begin
    add_anonymous_leaf (in_require (needed,[modref],None));
    option_iter (fun exp -> add_anonymous_leaf (in_import (modref,exp)))
      export
  end
  else
    add_anonymous_leaf (in_require (needed,[modref],export));
  if !Options.xml_export then !xml_require modref;
  add_frozen_state ()

(* the function called by Vernacentries.vernac_import *)

let import_module export (loc,qid) =
  try
    match Nametab.locate_module qid with
	MPfile dir -> 
	  if Lib.is_modtype () || Lib.is_module () || not export then
	    add_anonymous_leaf (in_import (dir, export))
	  else
	    add_anonymous_leaf (in_require ([],[dir], Some export))
      | mp ->
	  import_module export mp
  with
      Not_found ->
	user_err_loc
        (loc,"import_library",
	 str ((string_of_qualid qid)^" is not a module"))
  
(************************************************************************)
(*s Initializing the compilation of a library. *)

let start_library f = 
  let _,longf = 
    System.find_file_in_path (get_load_paths ()) (f^".v") in
  let ldir0 = find_logical_path (Filename.dirname longf) in
  let id = id_of_string (Filename.basename f) in
  let ldir = extend_dirpath ldir0 id in
  Declaremods.start_library ldir;
  ldir,longf

(************************************************************************)
(*s [save_library dir] ends library [dir] and save it to the disk. *)

let current_deps () =
  List.map (fun m -> (m.library_name, m.library_digest)) !libraries_loaded_list

let current_reexports () =
  List.map (fun m -> m.library_name) !libraries_exports_list

let save_library_to dir f =
  let cenv, seg = Declaremods.end_library dir in
  let md = { 
    md_name = dir;
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
  with e -> (warning ("Removed file "^f'); close_out ch; Sys.remove f'; raise e)

(************************************************************************)
(*s Display the memory use of a library. *)

open Printf

let mem s =
  let m = try_find_library s in
  h 0 (str (sprintf "%dk (cenv = %dk / seg = %dk)"
		 (size_kb m) (size_kb m.library_compiled) 
		 (size_kb m.library_objects)))
