(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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
  match list_filter2 (fun p d -> p = phys_dir) !load_path with
  | _,[dir] -> dir
  | _,[] -> Nameops.default_root_prefix
  | _,l -> anomaly ("Two logical paths are associated to "^phys_dir)

let remove_path dir =
  load_path := list_filter2 (fun p d -> p <> dir) !load_path

let add_load_path_entry (phys_path,coq_path) =
  let phys_path = canonical_path_name phys_path in
  match list_filter2 (fun p d -> p = phys_path) !load_path with
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

(***********************************************************************)
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

module CompilingModuleOrdered = 
  struct
    type t = dir_path
    let compare d1 d2 =
      Pervasives.compare
        (List.rev (repr_dirpath d1)) (List.rev (repr_dirpath d2))
  end

module CompilingModulemap = Map.Make(CompilingModuleOrdered)

(* This is a map from names to libraries *)
let libraries_table = ref CompilingModulemap.empty

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
  libraries_table := CompilingModulemap.empty;
  libraries_loaded_list := [];
  libraries_imports_list := [];
  libraries_exports_list := []

let _ = 
  Summary.declare_summary "MODULES"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_section = false }

let find_library s =
  try
    CompilingModulemap.find s !libraries_table
  with Not_found ->
    error ("Unknown library " ^ (string_of_dirpath s))

let library_full_filename m = (find_library m).library_filename

let library_is_loaded dir =
  try let _ = CompilingModulemap.find dir !libraries_table in true
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
  libraries_table := CompilingModulemap.add m.library_name m !libraries_table

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
(*s Operations on library objects and opening *)

(*let segment_rec_iter f =
  let rec apply = function
    | sp,Leaf obj -> f (sp,obj)
    | _,OpenedSection _ -> assert false
    | _,ClosedSection (_,_,seg) -> iter seg
    | _,(FrozenState _ | CompilingModule _ 
	| OpenedModule _ | OpenedModtype _) -> ()
  and iter seg =
    List.iter apply seg
  in
  iter

let segment_iter i v f =
  let rec apply = function
    | sp,Leaf obj -> f (i,sp,obj)
    | _,OpenedSection _ -> assert false
    | sp,ClosedSection (export,dir,seg) ->
	push_dir v dir (DirClosedSection dir);
	if export then iter seg
    | _,(FrozenState _ | CompilingModule _ 
	| OpenedModule _ | OpenedModtype _) -> ()
  and iter seg =
    List.iter apply seg
  in
  iter
*)

(*s [open_library s] opens a library. The library [s] and all libraries needed by
    [s] are assumed to be already loaded. When opening [s] we recursively open
    all the libraries needed by [s] and tagged [exported]. *) 

(*let open_objects i decls =
  segment_iter i (Exactly i) open_object decls*)

let open_library export m =
  if not (library_is_opened m.library_name) then begin
    register_open_library export m;
    Declaremods.import_module (MPfile m.library_name)
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
             (fun l m -> remember_last_of_each l (find_library m))
             [] m.library_imports
         in remember_last_of_each subimport m)
      [] modl in
  List.iter (open_library export) to_open_list


(************************************************************************)
(*s Loading from disk to cache (preparation phase) *)

let compunit_cache = ref CompilingModulemap.empty

let vo_magic_number = 0703 (* V7.3 *)

let (raw_extern_library, raw_intern_library) =
  System.raw_extern_intern vo_magic_number ".vo"

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
    let m = CompilingModulemap.find dir !libraries_table in
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

let mk_library md f digest = {
  library_name = md.md_name;
  library_filename = f;
  library_compiled = md.md_compiled;
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
    CompilingModulemap.find dir !libraries_table
  with Not_found ->
  try
    (* Look if already loaded in cache and consequently its dependencies *)
    CompilingModulemap.find dir !compunit_cache
  with Not_found ->
    (* [dir] is an absolute name which matches [f] which must be in loadpath *)
    let m = intern_from_file f in
    if dir <> m.library_name then
      errorlabstrm "load_physical_library"
	(str ("The file " ^ f ^ " contains library") ++ spc () ++
	 pr_dirpath m.library_name ++ spc () ++ str "and not library" ++
         spc() ++ pr_dirpath dir);
    compunit_cache := CompilingModulemap.add dir m !compunit_cache;
    List.iter (intern_mandatory_library dir) m.library_deps;
    m

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
    let m' = CompilingModulemap.find m.library_name !libraries_table in
    Options.if_verbose warning 
      ((string_of_dirpath m.library_name)^" is already loaded from file "^
       m'.library_filename);
    m.library_name
  with Not_found ->
    compunit_cache := CompilingModulemap.add m.library_name m !compunit_cache;
    List.iter (intern_mandatory_library m.library_name) m.library_deps;
    m.library_name

let locate_qualified_library qid =
  (* Look if loaded in current environment *)
  try 
    let dir = Nametab.locate_loaded_library qid in
    (LibLoaded, dir, library_full_filename dir)
  with Not_found ->
  (* Look if in loadpath *)
  try
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
    (LibInPath, extend_dirpath (find_logical_path path) base, file)
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


  The [read_library] operation is very similar, but has does not "open"
    the library
*)

type library_reference = dir_path list * bool option

let string_of_library (_,dir,_) = string_of_id (List.hd (repr_dirpath dir))

let rec load_library dir =
  try
    (* Look if loaded in current env (and consequently its dependencies) *)
    CompilingModulemap.find dir !libraries_table
  with Not_found ->
    (* [dir] is an absolute name matching [f] which must be in loadpath *)
    let m =
      try CompilingModulemap.find dir !compunit_cache
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
(*
    let mp = Global.import m.library_compiled_env m.library_digest in
    load_objects m.library_objects;
    Nametab.push_loaded_library m.library_name;
    (* TODO: chwilowy hak *)
    Declaremods.push_module_with_components m.module_name mp true;
    m
*)

let cache_require (_,(modl,export)) =
  let ml = list_map_left load_library modl in
  match export with
    | None -> ()
    | Some export -> open_libraries export ml

let load_require  _ (_,(modl,_)) =
  ignore(list_map_left load_library modl)

  (* keeps the require marker for closed section replay but removes
     OS dependent fields from .vo files for cross-platform compatibility *)
let export_require (l,e) = Some (List.map (fun d -> d) l,e)

let (in_require, out_require) =
  declare_object {(default_object "REQUIRE") with 
       cache_function = cache_require;
       load_function = load_require;
       export_function = export_require;
       classify_function = (fun (_,o) -> Anticipate o) }
 
let require_library spec qidl export =
(*
  if sections_are_opened () && Options.verbose () then
    warning ("Objets of "^(string_of_library modref)^
             " not surviving sections (e.g. Grammar \nand Hints)\n"^
             "will be removed at the end of the section");
*)
  let modrefl = List.map rec_intern_qualified_library qidl in
  add_anonymous_leaf (in_require (modrefl,Some export));
  add_frozen_state ()

let require_library_from_file spec idopt file export =
  let modref = rec_intern_library_from_file idopt file in
  add_anonymous_leaf (in_require ([modref],Some export));
  add_frozen_state ()

let import_library export (loc,qid) =
  let modref =
    try 
      Nametab.locate_loaded_library qid
    with Not_found ->
      user_err_loc
        (loc,"import_library",
	 str ((string_of_qualid qid)^" not loaded")) in
  add_anonymous_leaf (in_require ([modref],Some export))

let read_library qid =
  let modref = rec_intern_qualified_library qid in
  add_anonymous_leaf (in_require ([modref],None));
  add_frozen_state ()

let read_library_from_file f =
  let _, f = System.find_file_in_path (get_load_path ()) (f^".vo") in
  let modref = rec_intern_by_filename_only None f in
  add_anonymous_leaf (in_require ([modref],None));
  add_frozen_state ()

let reload_library (modrefl, export) =
  add_anonymous_leaf (in_require (modrefl,export));
  add_frozen_state ()


(***********************************************************************)
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
  let cenv, seg = Declaremods.export_library s in
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

(*s Iterators. *)

(*let fold_all_segments insec f x =
  let rec apply acc = function
    | sp, Leaf o -> f acc sp o
    | _, ClosedSection (_,_,seg) -> 
	if insec then List.fold_left apply acc seg else acc
    | _ -> acc
  in
  let acc' = 
    CompilingModulemap.fold 
      (fun _ m acc -> List.fold_left apply acc m.library_objects) 
      !libraries_table x
  in
  List.fold_left apply acc' (Lib.contents_after None)

let iter_all_segments insec f =
  let rec apply = function
    | sp, Leaf o -> f sp o
    | _, ClosedSection (_,_,seg) -> if insec then List.iter apply seg
    | _ -> ()
  in
  CompilingModulemap.iter 
    (fun _ m -> List.iter apply m.library_objects) !libraries_table;
  List.iter apply (Lib.contents_after None)
*)

(*s Pretty-printing of libraries state. *)
 
let fmt_libraries_state () =
  let opened = opened_libraries ()
  and loaded = loaded_libraries () in
  (str "Imported (open) Modules: " ++
     prlist_with_sep pr_spc pr_dirpath opened ++ fnl () ++
     str "Loaded Modules: " ++
     prlist_with_sep pr_spc pr_dirpath loaded ++ fnl ())

(*s Display the memory use of a library. *)

open Printf

let mem s =
  let m = find_library s in
  h 0 (str (sprintf "%dk (cenv = %dk / seg = %dk)"
		 (size_kb m) (size_kb m.library_compiled) 
		 (size_kb m.library_objects)))
