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
open Declaremods

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

(*s Modules loaded in memory contain the following informations. They are
    kept in the global table [modules_table]. *)

type module_t = {
  module_name : comp_unit_name;
  module_filename : System.physical_path;
  module_compiled_env : compiled_module;
  module_objects : mod_str_id * library_segment * library_segment;
  module_opened : bool;
  module_exported : bool;
  module_deps : (comp_unit_name * Digest.t * bool) list;
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

(*
let module_segment = function
  | None -> contents_after None
  | Some m -> (find_module m).module_objects
*)

let module_full_filename m = (find_module m).module_filename

let vo_magic_number = 0700

let (raw_extern_module, raw_intern_module) =
  System.raw_extern_intern vo_magic_number ".vo"

let segment_rec_iter f =
  let rec apply = function
    | sp,Leaf obj -> f (sp,obj)
    | _,OpenedSection _ -> assert false
    | _,ClosedSection (_,_,seg) -> iter seg
    | _,(FrozenState _ | CompUnit _) -> ()
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
    | _,(FrozenState _ | CompUnit _) -> ()
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
    Declaremods.import_module (MPcomp m.module_name);
    (* this should be done above *)
    (* open_objects m.module_declarations; *)
    let m = {m with module_opened = true} in
      modules_table := CompUnitmap.add m.module_name m !modules_table;
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


let check_locate_absolute_library dir =
  try
    locate_absolute_library dir
  with
  | LibUnmappedDir ->
      let prefix, dir = fst (split_dirpath dir), string_of_dirpath dir in
	errorlabstrm "load_module"
	  (str ("Cannot load "^dir^":") ++ spc () ++
	   str "no physical path bound to" ++ spc () ++ 
	   pr_dirpath prefix ++ fnl ())
  | LibNotFound ->
      errorlabstrm "load_module"
      (str"Cannot find module " ++ pr_dirpath dir ++ str" in loadpath")
  | _ -> assert false


let with_magic_number_check f a =
  try f a
  with System.Bad_magic_number fname ->
    errorlabstrm "load_module_from"
    (str"file " ++ str fname ++ spc () ++ str"has bad magic number." ++
     spc () ++ str"It is corrupted" ++ spc () ++
     str"or was compiled with another version of Coq." )

let rec load_module really = function
  | (LibLoaded, dir, _) ->
      CompUnitmap.find dir !modules_table
  | (LibInPath, dir, f) ->
    (* [dir] is an absolute name which matches [f] *)
    let md, deps, digest =
      try Stringmap.find f !compunit_cache
      with Not_found ->
      let ch = with_magic_number_check raw_intern_module f in
      let md = System.marshal_in ch in
      let deps = System.marshal_in ch in
      let digest = System.marshal_in ch in
      close_in ch;
      if dir <> md.md_name then
	errorlabstrm "load_module"
	  (str ("The file " ^ f ^ " contains module") ++ spc () ++
	   pr_dirpath md.md_name ++ spc () ++ str "and not module" ++ spc () ++
	   pr_dirpath dir) ;
      (match split_dirpath dir with
	| [], id -> Nametab.push_library_root id
	| _ -> ());
      compunit_cache := Stringmap.add f (md, deps, digest) !compunit_cache;
      (md, deps, digest) in
    intern_module really digest f md deps

and intern_module really digest fname md deps=
  let m = { module_name = md.md_name;
            module_filename = fname;
	    module_compiled_env = md.md_compiled_env;
	    module_objects = md.md_objects;
	    module_opened = false;
	    module_exported = false;
	    module_deps = deps;
	    module_digest = digest } in

  List.iter (load_mandatory_module really m.module_name) m.module_deps;
    
  if really then 
    Declaremods.register_comp_unit md digest
  else
    Declaremods.re_register_comp_unit md.md_name;

  modules_table := CompUnitmap.add md.md_name m !modules_table;
  m

and load_mandatory_module really caller (dir,d,_) =
  let m = load_module really (check_locate_absolute_library dir) in
  if d <> m.module_digest then
    error ("compiled module "^(string_of_dirpath caller)^
	   " makes inconsistent assumptions over module "
	   ^(string_of_dirpath dir))


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
	(str ("Cannot load "^(string_of_id id)^":") ++ spc () ++
	 str "no physical path bound to" ++ spc () ++ 
	 pr_dirpath prefix ++ fnl () )
  | LibNotFound ->
      errorlabstrm "load_module"
      (str"Cannot find module " ++ pr_qualid qid ++ str" in loadpath")
  | _ -> assert false

let check_module_short_name f dir = function
  | Some id when id <> snd (split_dirpath dir) ->
      errorlabstrm "load_module"
      (str ("The file " ^ f ^ " contains module") ++ spc () ++
       pr_dirpath dir ++ spc () ++ str "and not module" ++ spc () ++
       pr_id id)
  | _ -> ()

let locate_by_filename_only id f =
  let ch = with_magic_number_check raw_intern_module f in
  let md = System.marshal_in ch in
  let deps = System.marshal_in ch in
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
    compunit_cache := Stringmap.add f (md, deps, digest) !compunit_cache;
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


let reload_module (modref, export) =
  let m = load_module true modref in
  let m = {m with module_exported = true} in
    modules_table := CompUnitmap.add m.module_name m !modules_table;
  open_module false m.module_name


(*s [require_module] loads and opens a module. This is a synchronized
    operation. *)

type module_reference = (library_location * CompUnitmap.key * Util.Stringmap.key) * bool

let cache_require (_,(modref,export)) =
  let m = load_module true modref in
  let m = {m with module_exported = export} in
    modules_table := CompUnitmap.add m.module_name m !modules_table;
  open_module false m.module_name

let load_require  (_,(modref,_)) =
  ignore (load_module false modref)

let (in_require, out_require) =
  declare_object {(default_object "REQUIRE") with 
       cache_function = cache_require;
       load_function = load_require;
       classify_function = (fun (_,o) -> Anticipate o) 
     }
  

let require_module spec qid fileopt export =
(* Trop contraignant
  if sections_are_opened () then
    warning ("Objets of "^name^" not surviving sections (e.g. Grammar \nand Hints) will be removed at the end of the section");
*)
  let modref = locate_module qid fileopt in
  add_anonymous_leaf (in_require (modref,export));
  add_frozen_state ()


let cache_read (_,modref) = 
  let m = load_module true modref in
    modules_table := CompUnitmap.add m.module_name m !modules_table
  
let load_read (_,modref) = 
  ignore (load_module false modref)
  

let (in_read, out_read) =
  declare_object {(default_object "READ") with 
       cache_function = cache_read;
       load_function = load_read;
       classify_function = (fun (_,o) -> Anticipate o) 
     }


let read_module qid =
  let modref=locate_module qid None in
  add_anonymous_leaf (in_read modref);
  add_frozen_state ()

let read_module_from_file f =
  let _, f = System.find_file_in_path (get_load_path ()) (f^".vo") in
  let modref = (locate_by_filename_only None f) in
  add_anonymous_leaf (in_read modref);
  add_frozen_state ()



(*s [save_module s] saves the module [m] to the disk. *)

let current_imports () =
  CompUnitmap.fold
    (fun _ m l -> (m.module_name, m.module_digest, m.module_exported) :: l)
    !modules_table []

let save_module_to s f =
  let subst, keep = Lib.export_comp_unit s in
  let msid, cenv = Global.export s in
  let md = { 
    md_name = s;
    md_compiled_env = cenv;
    md_objects = msid, subst, keep}
  in
  let deps = current_imports ()  in
  let (f',ch) = raw_extern_module f in
  try
    System.marshal_out ch md;
    System.marshal_out ch deps;
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
    CompUnitmap.fold 
      (fun _ m acc -> List.fold_left apply acc m.module_objects) 
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
*)

(*s Pretty-printing of modules state. *)

let fmt_modules_state () =
  let opened = opened_modules ()
  and loaded = loaded_modules () in
  str "Imported (open) Modules: " ++
     prlist_with_sep pr_spc pr_dirpath opened  ++ fnl () ++
     str "Loaded Modules: " ++
     prlist_with_sep pr_spc pr_dirpath loaded  ++ fnl () 

(*s Display the memory use of a module. *)

open Printf

let mem s =
  let m = find_module s in
  h 0 (str (sprintf "%dk (cenv = %dk / seg = %dk)"
		 (size_kb m) (size_kb m.module_compiled_env) 
		 (size_kb m.module_objects))) 
