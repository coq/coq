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
open Nameops
open Environ
open Libobject
open Lib
open Nametab

(*s Load path. *)

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
          (* Assume the user is concerned by module naming *)
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

(*s Modules on disk contain the following informations (after the magic 
    number, and before the digest). *)

type compilation_unit_name = dir_path

type module_disk = { 
  md_name : compilation_unit_name;
  md_compiled_env : compiled_env;
  md_declarations : library_segment;
  md_deps : (compilation_unit_name * Digest.t) list;
  md_imports : compilation_unit_name list }

(*s Modules loaded in memory contain the following informations. They are
    kept in the global table [modules_table]. *)

type module_t = {
  module_name : compilation_unit_name;
  module_filename : System.physical_path;
  module_compiled_env : compiled_env;
  module_declarations : library_segment;
  module_deps : (compilation_unit_name * Digest.t) list;
  module_imports : compilation_unit_name list;
  module_digest : Digest.t }

module CompUnitOrdered = 
  struct
    type t = dir_path
    let compare d1 d2 =
      Pervasives.compare
        (List.rev (repr_dirpath d1)) (List.rev (repr_dirpath d2))
  end

module CompUnitmap = Map.Make(CompUnitOrdered)

(* This is a map from names to modules *)
let modules_table = ref CompUnitmap.empty

(* These are the _ordered_ lists of loaded, imported and exported modules *)
let modules_loaded_list = ref []
let modules_imports_list = ref []
let modules_exports_list = ref []

let freeze () =
  !modules_table,
  !modules_loaded_list,
  !modules_imports_list,
  !modules_exports_list

let unfreeze (mt,mo,mi,me) = 
  modules_table := mt;
  modules_loaded_list := mo;
  modules_imports_list := mi;
  modules_exports_list := me

let init () =
  modules_table := CompUnitmap.empty;
  modules_loaded_list := [];
  modules_imports_list := [];
  modules_exports_list := []

let _ = 
  Summary.declare_summary "MODULES"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_section = false }

let find_module s =
  try
    CompUnitmap.find s !modules_table
  with Not_found ->
    error ("Unknown module " ^ (string_of_dirpath s))

let module_is_loaded dir =
  try let _ = CompUnitmap.find dir !modules_table in true
  with Not_found -> false

let module_is_opened dir = 
  List.exists (fun m -> m.module_name = dir) !modules_imports_list

let module_is_exported dir =
  List.exists (fun m -> m.module_name = dir) !modules_exports_list

let loaded_modules () = 
  List.map (fun m -> m.module_name) !modules_loaded_list

let opened_modules () =
  List.map (fun m -> m.module_name) !modules_imports_list

  (* If a module is loaded several time, then the first occurrence must
     be performed first, thus the modules_loaded_list ... *)

let register_loaded_module m =
  let rec aux = function
    | [] -> [m]
    | m'::_ as l when m'.module_name = m.module_name -> l
    | m'::l' -> m' :: aux l' in
  modules_loaded_list := aux !modules_loaded_list;
  modules_table := CompUnitmap.add m.module_name m !modules_table

  (* ... while if a module is imported/exported several time, then
     only the last occurrence is really needed - though the imported
     list may differ from the exported list (consider the sequence
     Export A; Export B; Import A which results in A;B for exports but
     in B;A for imports) *)

let rec remember_last_of_each l m =
  match l with
  | [] -> [m]
  | m'::l' when m'.module_name = m.module_name -> remember_last_of_each l' m
  | m'::l' -> m' :: remember_last_of_each l' m

let register_open_module export m =
  modules_imports_list := remember_last_of_each !modules_imports_list m;
  if export then 
    modules_exports_list := remember_last_of_each !modules_exports_list m

let compunit_cache = ref CompUnitmap.empty

let module_segment = function
  | None -> contents_after None
  | Some m -> (find_module m).module_declarations

let module_full_filename m = (find_module m).module_filename

let vo_magic_number = 0702 (* V7.2 *)

let (raw_extern_module, raw_intern_module) =
  System.raw_extern_intern vo_magic_number ".vo"

let segment_rec_iter f =
  let rec apply = function
    | sp,Leaf obj -> f (sp,obj)
    | _,OpenedSection _ -> assert false
    | _,ClosedSection (_,_,seg) -> iter seg
    | _,(FrozenState _ | Module _) -> ()
  and iter seg =
    List.iter apply seg
  in
  iter

let segment_iter f =
  let rec apply = function
    | sp,Leaf obj -> f (sp,obj)
    | _,OpenedSection _ -> assert false
    | sp,ClosedSection (export,dir,seg) ->
	push_section dir;
	if export then iter seg
    | _,(FrozenState _ | Module _) -> ()
  and iter seg =
    List.iter apply seg
  in
  iter

(*s [open_module s] opens a module. The module [s] and all modules needed by
    [s] are assumed to be already loaded. When opening [s] we recursively open
    all the modules needed by [s] and tagged [exported]. *) 

let open_objects decls =
  segment_iter open_object decls

let open_module export m =
  if not (module_is_opened m.module_name) then
    (register_open_module export m;
     open_objects m.module_declarations)
  else
    if export then 
      modules_exports_list := remember_last_of_each !modules_exports_list m

let open_modules export modl = 
  let to_open_list = 
    List.fold_left
      (fun l m ->
         let subimport =
           List.fold_left
             (fun l m -> remember_last_of_each l (find_module m))
             [] m.module_imports
         in remember_last_of_each subimport m)
      [] modl in
  List.iter (open_module export) to_open_list

(*s [load_module s] loads the module [s] from the disk, and [find_module s]
   returns the module of name [s], loading it if necessary. 
   The boolean [doexp] specifies if we open the modules which are declared
   exported in the dependencies (it is [true] at the highest level;
   then same value as for caller is reused in recursive loadings). *)

let load_objects decls =
  segment_iter load_object decls

exception LibUnmappedDir
exception LibNotFound
type library_location = LibLoaded | LibInPath

let locate_absolute_library dir =
  (* Look if loaded in current environment *)
  try
    let m = CompUnitmap.find dir !modules_table in
    (dir, m.module_filename)
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

let rec load_module dir =
  try
    (* Look if loaded in current env (and consequently its dependencies) *)
    CompUnitmap.find dir !modules_table
  with Not_found ->
    (* [dir] is an absolute name which matches [f] which must be in loadpath *)
    let m =
      try CompUnitmap.find dir !compunit_cache
      with Not_found ->
        anomaly ((string_of_dirpath dir)^" should be in cache")
    in
    List.iter (fun (dir,_) -> ignore (load_module dir)) m.module_deps;
    Global.import m.module_compiled_env;
    load_objects m.module_declarations;
    register_loaded_module m;
    Nametab.push_loaded_library m.module_name;
    m

let mk_module md f digest = {
  module_name = md.md_name;
  module_filename = f;
  module_compiled_env = md.md_compiled_env;
  module_declarations = md.md_declarations;
  module_deps = md.md_deps;
  module_imports = md.md_imports;
  module_digest = digest }

let intern_from_file f =
  let ch = with_magic_number_check raw_intern_module f in
  let md = System.marshal_in ch in
  let digest = System.marshal_in ch in
  close_in ch;
  mk_module md f digest

let rec intern_module (dir, f) =
  try
    (* Look if in the current logical environment *)
    CompUnitmap.find dir !modules_table
  with Not_found ->
  try
    (* Look if already loaded in cache and consequently its dependencies *)
    CompUnitmap.find dir !compunit_cache
  with Not_found ->
    (* [dir] is an absolute name which matches [f] which must be in loadpath *)
    let m = intern_from_file f in
    if dir <> m.module_name then
      errorlabstrm "load_physical_module"
	(str ("The file " ^ f ^ " contains module") ++ spc () ++
	 pr_dirpath m.module_name ++ spc () ++ str "and not module" ++
         spc() ++ pr_dirpath dir);
    compunit_cache := CompUnitmap.add dir m !compunit_cache;
    List.iter (intern_mandatory_module dir) m.module_deps;
    m

and intern_mandatory_module caller (dir,d) =
  let m = intern_absolute_module_from dir in
  if d <> m.module_digest then
    error ("compiled module "^(string_of_dirpath caller)^
	   " makes inconsistent assumptions over module "
	   ^(string_of_dirpath dir))

and intern_absolute_module_from dir =
  try
    intern_module (locate_absolute_library dir)
  with
  | LibUnmappedDir ->
      let prefix, dir = fst (split_dirpath dir), string_of_dirpath dir in
      errorlabstrm "load_absolute_module_from"
      (str ("Cannot load "^dir^":") ++ spc () ++ 
      str "no physical path bound to" ++ spc () ++ pr_dirpath prefix ++ fnl ())
  | LibNotFound ->
      errorlabstrm "load_absolute_module_from"
      (str"Cannot find module " ++ pr_dirpath dir ++ str" in loadpath")
  | e -> raise e

let rec_intern_module mref = let _ = intern_module mref in ()

let check_module_short_name f dir = function
  | Some id when id <> snd (split_dirpath dir) ->
      errorlabstrm "check_module_short_name"
      (str ("The file " ^ f ^ " contains module") ++ spc () ++
      pr_dirpath dir ++ spc () ++ str "and not module" ++ spc () ++
      pr_id id)
  | _ -> ()

let rec_intern_by_filename_only id f =
  let m = intern_from_file f in
  (* Only the base name is expected to match *)
  check_module_short_name f m.module_name id;
  (* We check no other file containing same module is loaded *)
  try
    let m' = CompUnitmap.find m.module_name !modules_table in
    Options.if_verbose warning 
      ((string_of_dirpath m.module_name)^" is already loaded from file "^
       m'.module_filename);
    m.module_name
  with Not_found ->
    compunit_cache := CompUnitmap.add m.module_name m !compunit_cache;
    List.iter (intern_mandatory_module m.module_name) m.module_deps;
    m.module_name

let locate_qualified_library qid =
  (* Look if loaded in current environment *)
  try 
    let dir = Nametab.locate_loaded_library qid in
    (LibLoaded, dir, module_full_filename dir)
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

let rec_intern_qualified_library qid =
  try
    let (_,dir,f) = locate_qualified_library qid in
    rec_intern_module (dir,f);
    dir
  with
  | LibUnmappedDir ->
      let prefix, id = repr_qualid qid in
      errorlabstrm "rec_intern_qualified_library"
      (str ("Cannot load "^(string_of_id id)^":") ++ spc () ++ 
      str "no physical path bound to" ++ spc () ++ pr_dirpath prefix ++ fnl ())
  | LibNotFound ->
      errorlabstrm "rec_intern_qualified_library"
      (str"Cannot find module " ++ pr_qualid qid ++ str" in loadpath")

let rec_intern_module_from_file qid f =
  (* A name is specified, we have to check it contains module id *)
  let prefix, id = repr_qualid qid in
  assert (repr_dirpath prefix = []);
  let _, f = System.find_file_in_path (get_load_path ()) (f^".vo") in
  rec_intern_by_filename_only (Some id) f

(*s [require_module] loads and opens a module. This is a synchronized
    operation. *)

type module_reference = dir_path list * bool option

let string_of_module (_,dir,_) = string_of_id (List.hd (repr_dirpath dir))

let cache_require (_,(modl,export)) =
  let ml = list_map_left load_module modl in
  match export with
    | None -> ()
    | Some export -> open_modules export ml

  (* keeps the require marker for closed section replay but removes
     OS dependent fields from .vo files for cross-platform compatibility *)
let export_require (l,e) = Some (List.map (fun d -> d) l,e)

let (in_require, out_require) =
  declare_object
    ("REQUIRE",
     { cache_function = cache_require;
       load_function = (fun _ -> ());
       open_function = (fun _ -> ());
       export_function = export_require })
 
let require_module spec qidl export =
(*
  if sections_are_opened () && Options.verbose () then
    warning ("Objets of "^(string_of_module modref)^
             " not surviving sections (e.g. Grammar \nand Hints)\n"^
             "will be removed at the end of the section");
*)
  let modrefl = List.map rec_intern_qualified_library qidl in
  add_anonymous_leaf (in_require (modrefl,Some export));
  add_frozen_state ()

let require_module_from_file spec qid file export =
  let modref = rec_intern_module_from_file qid file in
  add_anonymous_leaf (in_require ([modref],Some export));
  add_frozen_state ()

let import_module export qid =
  let modref =
    try 
      Nametab.locate_loaded_library qid
    with Not_found ->
      error ((Nametab.string_of_qualid qid)^" not loaded") in
  add_anonymous_leaf (in_require ([modref],Some export))

let read_module qid =
  let modref = rec_intern_qualified_library qid in
  add_anonymous_leaf (in_require ([modref],None));
  add_frozen_state ()

let read_module_from_file f =
  let _, f = System.find_file_in_path (get_load_path ()) (f^".vo") in
  let modref = rec_intern_by_filename_only None f in
  add_anonymous_leaf (in_require ([modref],None));
  add_frozen_state ()

let reload_module (modrefl, export) =
  add_anonymous_leaf (in_require (modrefl,export));
  add_frozen_state ()

(*s [save_module s] saves the module [m] to the disk. *)

let current_deps () =
  List.map (fun m -> (m.module_name, m.module_digest)) !modules_loaded_list

let current_reexports () =
  List.map (fun m -> m.module_name) !modules_exports_list

let save_module_to s f =
  let seg = export_module s in
  let md = { 
    md_name = s;
    md_compiled_env = Global.export s;
    md_declarations = seg;
    md_deps = current_deps ();
    md_imports = current_reexports () } in
  let (f',ch) = raw_extern_module f in
  try
    System.marshal_out ch md;
    flush ch;
    let di = Digest.file f' in
    System.marshal_out ch di;
    close_out ch
  with e -> (warning ("Removed file "^f');close_out ch; Sys.remove f'; raise e)

(*s Iterators. *)

let fold_all_segments insec f x =
  let rec apply acc = function
    | sp, Leaf o -> f acc sp o
    | _, ClosedSection (_,_,seg) -> 
	if insec then List.fold_left apply acc seg else acc
    | _ -> acc
  in
  let acc' = 
    CompUnitmap.fold 
      (fun _ m acc -> List.fold_left apply acc m.module_declarations) 
      !modules_table x
  in
  List.fold_left apply acc' (Lib.contents_after None)

let iter_all_segments insec f =
  let rec apply = function
    | sp, Leaf o -> f sp o
    | _, ClosedSection (_,_,seg) -> if insec then List.iter apply seg
    | _ -> ()
  in
  CompUnitmap.iter 
    (fun _ m -> List.iter apply m.module_declarations) !modules_table;
  List.iter apply (Lib.contents_after None)

(*s Pretty-printing of modules state. *)

let fmt_modules_state () =
  let opened = opened_modules ()
  and loaded = loaded_modules () in
  (str "Imported (open) Modules: " ++
     prlist_with_sep pr_spc pr_dirpath opened ++ fnl () ++
     str "Loaded Modules: " ++
     prlist_with_sep pr_spc pr_dirpath loaded ++ fnl ())

(*s Display the memory use of a module. *)

open Printf

let mem s =
  let m = find_module s in
  h 0 (str (sprintf "%dk (cenv = %dk / seg = %dk)"
		 (size_kb m) (size_kb m.module_compiled_env) 
		 (size_kb m.module_declarations)))
