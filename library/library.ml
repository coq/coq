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

open Identifier
open Names
open Safe_env
open Libnames
open Libobject
open Lib
open Nametab

(*s Load path. *)

type logical_path = dir_path

let load_path = ref ([],[] : System.physical_path list * logical_path list)

let get_load_path () = fst !load_path

let find_logical_path dir = 
  match list_filter2 (fun p d -> p = dir) !load_path with
  | _,[dir] -> dir
  | _ -> anomaly ("Two logical paths are associated to "^dir)

let remove_path dir =
  load_path := list_filter2 (fun p d -> p <> dir) !load_path

let add_load_path_entry (phys_path,coq_path) =
  match list_filter2 (fun p d -> p = phys_path) !load_path with
  | _,[dir] ->
      if dir <> coq_path && coq_path <> Nametab.default_root_prefix then
	  (* Assume the user is concerned by module naming *)
	begin
	  if dir <> Nametab.default_root_prefix then
	    warning (phys_path^" was previously bound to "
	    ^(string_of_dirpath dir)
	    ^("\nIt is remapped to "^(string_of_dirpath coq_path)));
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
  md_compiled_env : compiled_module;
  md_declarations : library_segment;
  md_deps : (compilation_unit_name * Digest.t * bool) list }

(*s Modules loaded in memory contain the following informations. They are
    kept in the global table [modules_table]. *)

type module_t = {
  module_name : compilation_unit_name;
  module_filename : System.physical_path;
  module_compiled_env : compiled_module;
  module_declarations : library_segment;
  mutable module_opened : bool;
  mutable module_exported : bool;
  module_deps : (compilation_unit_name * Digest.t * bool) list;
  module_digest : Digest.t }

module CompUnitOrdered = 
  struct
    type t = dir_path
    let compare = Pervasives.compare
  end

module CompUnitmap = Map.Make(CompUnitOrdered)

let modules_table = ref CompUnitmap.empty

let _ = 
  Summary.declare_summary "MODULES"
    { Summary.freeze_function = (fun () -> !modules_table);
      Summary.unfreeze_function = (fun ft -> modules_table := ft);
      Summary.init_function = (fun () -> modules_table := CompUnitmap.empty);
      Summary.survive_section = false }

let find_module s =
  try
    CompUnitmap.find s !modules_table
  with Not_found ->
    error ("Unknown module " ^ (string_of_dirpath s))

let module_is_loaded dir =
  try let _ = CompUnitmap.find dir !modules_table in true
  with Not_found -> false

let module_is_opened s = (find_module [id_of_string s]).module_opened

let loaded_modules () =
  CompUnitmap.fold (fun s _ l -> s :: l) !modules_table []

let opened_modules () =
  CompUnitmap.fold 
    (fun s m l -> if m.module_opened then s :: l else l) 
    !modules_table []

let compunit_cache = ref Stringmap.empty

let module_segment = function
  | None -> contents_after None
  | Some m -> (find_module m).module_declarations

let module_full_filename m = (find_module m).module_filename

let vo_magic_number = 0700

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
    | sp,ClosedSection (export,s,seg) ->
	push_section (wd_of_sp sp);
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

let rec open_module force s =
  let m = find_module s in
  if force or not m.module_opened then begin
    List.iter (fun (m,_,exp) -> if exp then open_module force m) m.module_deps;
    open_objects m.module_declarations;
    m.module_opened <- true
  end

let import_module = open_module true

(*s [load_module s] loads the module [s] from the disk, and [find_module s]
   returns the module of name [s], loading it if necessary. 
   The boolean [doexp] specifies if we open the modules which are declared
   exported in the dependencies (it is [true] at the highest level;
   then same value as for caller is reused in recursive loadings). *)

let load_objects decls =
(*  segment_rec_iter load_object decls*)
  segment_iter load_object decls

exception LibUnmappedDir
exception LibNotFound
type library_location = LibLoaded | LibInPath

let locate_absolute_library dir =
  (* Look if loaded *)
  try
    let m = CompUnitmap.find dir !modules_table in
    (LibLoaded, dir, m.module_filename)
  with Not_found ->
  (* Look if in loadpath *)
  try
    let pref, base = split_dirpath dir in
    let loadpath = load_path_of_logical_path pref in
    if loadpath = [] then raise LibUnmappedDir;
    let name = (string_of_id base)^".vo" in
    let _, file = System.where_in_path loadpath name in
    (LibInPath, dir, file)
  with Not_found ->  raise LibNotFound

let with_magic_number_check f a =
  try f a
  with System.Bad_magic_number fname ->
    errorlabstrm "load_module_from"
    [< 'sTR"file "; 'sTR fname; 'sPC; 'sTR"has bad magic number.";
    'sPC; 'sTR"It is corrupted"; 'sPC;
    'sTR"or was compiled with another version of Coq." >]

let rec load_module = function
  | (LibLoaded, dir, _) ->
      CompUnitmap.find dir !modules_table
  | (LibInPath, dir, f) ->
    (* [dir] is an absolute name which matches [f] *)
    let md, digest =
      try Stringmap.find f !compunit_cache
      with Not_found ->
      let ch = with_magic_number_check raw_intern_module f in
      let md = System.marshal_in ch in
      let digest = System.marshal_in ch in
      close_in ch;
      if dir <> md.md_name then
	errorlabstrm "load_module"
	  [< 'sTR ("The file " ^ f ^ " contains module"); 'sPC;
	  pr_dirpath md.md_name; 'sPC; 'sTR "and not module"; 'sPC;
	  pr_dirpath dir >];
      (match split_dirpath dir with
	| [], id -> Nametab.push_library_root id
	| _ -> ());
      compunit_cache := Stringmap.add f (md, digest) !compunit_cache;
      (md, digest) in
    intern_module digest f md

and intern_module digest fname md =
  let m = { module_name = md.md_name;
            module_filename = fname;
	    module_compiled_env = md.md_compiled_env;
	    module_declarations = md.md_declarations;
	    module_opened = false;
	    module_exported = false;
	    module_deps = md.md_deps;
	    module_digest = digest } in
  List.iter (load_mandatory_module md.md_name) m.module_deps;
  let mp = Global.import m.module_compiled_env digest in
  load_objects m.module_declarations;
  modules_table := CompUnitmap.add md.md_name m !modules_table;
  Nametab.push_loaded_library md.md_name;
(* TODO: revise this! *)
  Declare.declare_module_components m.module_name mp;
  m

and load_mandatory_module caller (dir,d,_) =
  let m = load_absolute_module_from dir in
  if d <> m.module_digest then
    error ("compiled module "^(string_of_dirpath caller)^
	   " makes inconsistent assumptions over module "
	   ^(string_of_dirpath dir))

and load_absolute_module_from dir =
  try
    load_module (locate_absolute_library dir)
  with
  | LibUnmappedDir ->
      let prefix, dir = fst (split_dirpath dir), string_of_dirpath dir in
      errorlabstrm "load_module"
      [< 'sTR ("Cannot load "^dir^":"); 'sPC; 
      'sTR "no physical path bound to"; 'sPC; pr_dirpath prefix; 'fNL >]
  | LibNotFound ->
      errorlabstrm "load_module"
      [< 'sTR"Cannot find module "; pr_dirpath dir; 'sTR" in loadpath">]
  | _ -> assert false

let try_locate_qualified_library qid =
  (* Look if loaded *)
  try 
    let dir = Nametab.locate_loaded_library qid in
    (LibLoaded, dir, module_full_filename dir)
  with Not_found ->
  (* Look if in loadpath *)
  try
    let dir, base = repr_qualid qid in 
    let loadpath =
      if dir = [] then get_load_path ()
      else if is_absolute_dirpath dir then
	load_path_of_logical_path dir
      else
	error
	  ("Not loaded partially qualified library names not implemented: "
	  ^(string_of_qualid qid))
    in
    if loadpath = [] then raise LibUnmappedDir;
    let name =  (string_of_id base)^".vo" in
    let path, file = System.where_in_path loadpath name in
    (LibInPath, find_logical_path path@[base], file)
  with Not_found -> raise LibNotFound

let locate_qualified_library qid =
  try
    try_locate_qualified_library qid
  with
  | LibUnmappedDir ->
      let prefix, id = repr_qualid qid in
      errorlabstrm "load_module"
      [< 'sTR ("Cannot load "^(string_of_id id)^":"); 'sPC; 
      'sTR "no physical path bound to"; 'sPC; pr_dirpath prefix; 'fNL >]
  | LibNotFound ->
      errorlabstrm "load_module"
      [< 'sTR"Cannot find module "; pr_qualid qid; 'sTR" in loadpath">]
  | _ -> assert false

let check_module_short_name f dir = function
  | Some id when id <> snd (split_dirpath dir) ->
      errorlabstrm "load_module"
      [< 'sTR ("The file " ^ f ^ " contains module"); 'sPC;
      pr_dirpath dir; 'sPC; 'sTR "and not module"; 'sPC;
      pr_id id >]
  | _ -> ()

let locate_by_filename_only id f =
  let ch = with_magic_number_check raw_intern_module f in
  let md = System.marshal_in ch in
  let digest = System.marshal_in ch in
  close_in ch;
  (* Only the base name is expected to match *)
  check_module_short_name f md.md_name id;
  (* We check no other file containing same module is loaded *)
  try
    let m = CompUnitmap.find md.md_name !modules_table in
    warning ((string_of_dirpath md.md_name)^" is already loaded from file "^
    m.module_filename);
    (LibLoaded, md.md_name, m.module_filename)
  with Not_found ->
    (match split_dirpath md.md_name with
      | [], id -> Nametab.push_library_root id
      | _ -> ());
    compunit_cache := Stringmap.add f (md, digest) !compunit_cache;
    (LibInPath, md.md_name, f)

let locate_module qid = function
  | Some f ->
      (* A name is specified, we have to check it contains module id *)
      let prefix, id = repr_qualid qid in
      assert (prefix = []);
      let _, f = System.find_file_in_path (get_load_path ()) (f^".vo") in
      locate_by_filename_only (Some id) f
  | None ->
      (* No name, we need to find the file name *)
      locate_qualified_library qid

let read_module qid =
  ignore (load_module (locate_qualified_library qid))

let read_module_from_file f =
  let _, f = System.find_file_in_path (get_load_path ()) (f^".vo") in
  ignore (load_module (locate_by_filename_only None f))

let reload_module (modref, export) =
  let m = load_module modref in
  if export then m.module_exported <- true;
  open_module false m.module_name

(*s [require_module] loads and opens a module. This is a synchronized
    operation. *)

type module_reference = (library_location * CompUnitmap.key * Util.Stringmap.key) * bool

let cache_require (_,(modref,export)) =
  let m = load_module modref in
  if export then m.module_exported <- true;
  open_module false m.module_name

let (in_require, out_require) =
  declare_object
    ("REQUIRE",
     { cache_function = cache_require;
       load_function = (fun _ -> ());
       open_function = (fun _ -> ());
       export_function = (fun _ -> None) })
  
let require_module spec qid fileopt export =
(* Trop contraignant
  if sections_are_opened () then
    warning ("Objets of "^name^" not surviving sections (e.g. Grammar \nand Hints) will be removed at the end of the section");
*)
  let modref = locate_module qid fileopt in
  add_anonymous_leaf (in_require (modref,export));
  add_frozen_state ()

(*s [save_module s] saves the module [m] to the disk. *)

let current_imports () =
  CompUnitmap.fold
    (fun _ m l -> (m.module_name, m.module_digest, m.module_exported) :: l)
    !modules_table []

let save_module_to s f =
  let seg = export_module s in
  let md = { 
    md_name = s;
    md_compiled_env = Global.export s;
    md_declarations = seg;
    md_deps = current_imports () } in
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
  [< 'sTR "Imported (open) Modules: " ;
     prlist_with_sep pr_spc pr_dirpath opened ; 'fNL ;
     'sTR "Loaded Modules: ";
     prlist_with_sep pr_spc pr_dirpath loaded ; 'fNL >]

(*s Display the memory use of a module. *)

open Printf

let mem s =
  let m = find_module s in
  h 0 [< 'sTR (sprintf "%dk (cenv = %dk / seg = %dk)"
		 (size_kb m) (size_kb m.module_compiled_env) 
		 (size_kb m.module_declarations)) >]
