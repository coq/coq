(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Names

let pr_dirpath dp = str (string_of_dirpath dp)
let default_root_prefix = make_dirpath []
let split_dirpath d =
  let l = repr_dirpath d in (make_dirpath (List.tl l), List.hd l)
let extend_dirpath p id = make_dirpath (id :: repr_dirpath p)

type section_path = {
  dirpath : string list ;
  basename : string }
let dir_of_path p =
  make_dirpath (List.map id_of_string p.dirpath)
let path_of_dirpath dir =
  match repr_dirpath dir with
      [] -> failwith "path_of_dirpath"
    | l::dir ->
        {dirpath=List.map string_of_id dir;basename=string_of_id l}
let pr_dirlist dp =
  prlist_with_sep (fun _ -> str".") str (List.rev dp)
let pr_path sp =
  match sp.dirpath with
      [] -> str sp.basename
    | sl -> pr_dirlist sl ++ str"." ++ str sp.basename

type library_objects

type compilation_unit_name = dir_path

type library_disk = {
  md_name : compilation_unit_name;
  md_compiled : Safe_typing.LightenLibrary.lightened_compiled_library;
  md_objects : library_objects;
  md_deps : (compilation_unit_name * Digest.t) list;
  md_imports : compilation_unit_name list }

(************************************************************************)
(*s Modules on disk contain the following informations (after the magic
    number, and before the digest). *)

(*s Modules loaded in memory contain the following informations. They are
    kept in the global table [libraries_table]. *)

type library_t = {
  library_name : compilation_unit_name;
  library_filename : System.physical_path;
  library_compiled : Safe_typing.compiled_library;
  library_deps : (compilation_unit_name * Digest.t) list;
  library_digest : Digest.t }

module LibraryOrdered =
  struct
    type t = dir_path
    let compare d1 d2 =
      Pervasives.compare
        (List.rev (repr_dirpath d1)) (List.rev (repr_dirpath d2))
  end

module LibrarySet = Set.Make(LibraryOrdered)
module LibraryMap = Map.Make(LibraryOrdered)

(* This is a map from names to loaded libraries *)
let libraries_table = ref LibraryMap.empty

(* various requests to the tables *)

let find_library dir =
  LibraryMap.find dir !libraries_table

let try_find_library dir =
  try find_library dir
  with Not_found ->
    error ("Unknown library " ^ (string_of_dirpath dir))

let library_full_filename dir = (find_library dir).library_filename

  (* If a library is loaded several time, then the first occurrence must
     be performed first, thus the libraries_loaded_list ... *)

let register_loaded_library m =
  libraries_table := LibraryMap.add m.library_name m !libraries_table

let check_one_lib admit (dir,m) =
  let file = m.library_filename in
  let md = m.library_compiled in
  let dig = m.library_digest in
  (* Look up if the library is to be admitted correct. We could
     also check if it carries a validation certificate (yet to
     be implemented). *)
  if LibrarySet.mem dir admit then
    (Flags.if_verbose msgnl
      (str "Admitting library: " ++ pr_dirpath dir);
      Safe_typing.unsafe_import file md dig)
  else
    (Flags.if_verbose msgnl
      (str "Checking library: " ++ pr_dirpath dir);
      Safe_typing.import file md dig);
  Flags.if_verbose msg(fnl());
  register_loaded_library m

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
  | _,[] -> default_root_prefix
  | _,l -> anomaly ("Two logical paths are associated to "^phys_dir)

let remove_load_path dir =
  load_paths := list_filter2 (fun p d -> p <> dir) !load_paths

let add_load_path (phys_path,coq_path) =
  if !Flags.debug then
    msgnl (str "path: " ++ pr_dirpath coq_path ++ str " ->" ++ spc() ++
           str phys_path);
  let phys_path = canonical_path_name phys_path in
    match list_filter2 (fun p d -> p = phys_path) !load_paths with
      | _,[dir] ->
	  if coq_path <> dir
            (* If this is not the default -I . to coqtop *)
            && not
            (phys_path = canonical_path_name Filename.current_dir_name
		&& coq_path = default_root_prefix)
	  then
	    begin
              (* Assume the user is concerned by library naming *)
	      if dir <> default_root_prefix then
		Flags.if_warn msg_warning
		  (str phys_path ++ strbrk " was previously bound to " ++
		   pr_dirpath dir ++ strbrk "; it is remapped to " ++
		   pr_dirpath coq_path);
	      remove_load_path phys_path;
	      load_paths := (phys_path::fst !load_paths, coq_path::snd !load_paths)
	    end
      | _,[] ->
	  load_paths := (phys_path :: fst !load_paths, coq_path :: snd !load_paths)
      | _ -> anomaly ("Two logical paths are associated to "^phys_path)

let load_paths_of_dir_path dir =
  fst (list_filter2 (fun p d -> d = dir) !load_paths)

(************************************************************************)
(*s Locate absolute or partially qualified library names in the path *)

exception LibUnmappedDir
exception LibNotFound

let locate_absolute_library dir =
  (* Search in loadpath *)
  let pref, base = split_dirpath dir in
  let loadpath = load_paths_of_dir_path pref in
  if loadpath = [] then raise LibUnmappedDir;
  try
    let name = string_of_id base^".vo" in
    let _, file = System.where_in_path ~warn:false loadpath name in
    (dir, file)
  with Not_found ->
  (* Last chance, removed from the file system but still in memory *)
  try
    (dir, library_full_filename dir)
  with Not_found ->
    raise LibNotFound

let locate_qualified_library qid =
  try
    let loadpath =
      (* Search library in loadpath *)
      if qid.dirpath=[] then get_load_paths ()
      else
        (* we assume qid is an absolute dirpath *)
        load_paths_of_dir_path (dir_of_path qid)
    in
    if loadpath = [] then raise LibUnmappedDir;
    let name =  qid.basename^".vo" in
    let path, file = System.where_in_path loadpath name in
    let dir =
      extend_dirpath (find_logical_path path) (id_of_string qid.basename) in
    (* Look if loaded *)
    try
      (dir, library_full_filename dir)
    with Not_found ->
      (dir, file)
  with Not_found -> raise LibNotFound

let explain_locate_library_error qid = function
  | LibUnmappedDir ->
      let prefix = qid.dirpath in
      errorlabstrm "load_absolute_library_from"
      (str "Cannot load " ++ pr_path qid ++ str ":" ++ spc () ++
      str "no physical path bound to" ++ spc () ++ pr_dirlist prefix ++ fnl ())
  | LibNotFound ->
      errorlabstrm "load_absolute_library_from"
      (str"Cannot find library " ++ pr_path qid ++ str" in loadpath")
  | e -> raise e

let try_locate_absolute_library dir =
  try
    locate_absolute_library dir
  with e ->
    explain_locate_library_error (path_of_dirpath dir) e

let try_locate_qualified_library qid =
  try
    locate_qualified_library qid
  with e ->
    explain_locate_library_error qid e

(************************************************************************)
(*s Low-level interning/externing of libraries to files *)

(*s Loading from disk to cache (preparation phase) *)

let raw_intern_library =
  snd (System.raw_extern_intern Coq_config.vo_magic_number ".vo")

let with_magic_number_check f a =
  try f a
  with System.Bad_magic_number fname ->
    errorlabstrm "with_magic_number_check"
    (str"file " ++ str fname ++ spc () ++ str"has bad magic number." ++
    spc () ++ str"It is corrupted" ++ spc () ++
    str"or was compiled with another version of Coq.")

(************************************************************************)
(* Internalise libraries *)

let mk_library md f table digest = {
  library_name = md.md_name;
  library_filename = f;
  library_compiled = Safe_typing.LightenLibrary.load table md.md_compiled;
  library_deps = md.md_deps;
  library_digest = digest }

let name_clash_message dir mdir f =
  str ("The file " ^ f ^ " contains library") ++ spc () ++
  pr_dirpath mdir ++ spc () ++ str "and not library" ++ spc() ++
  pr_dirpath dir

(* Dependency graph *)
let depgraph = ref LibraryMap.empty

let intern_from_file (dir, f) =
  Flags.if_verbose msg (str"[intern "++str f++str" ...");
  let (md,table,digest) =
    try
      let ch = with_magic_number_check raw_intern_library f in
      let (md:library_disk) = System.marshal_in ch in
      let digest = System.marshal_in ch in
      let table = (System.marshal_in ch : Safe_typing.LightenLibrary.table) in
      close_in ch;
      if dir <> md.md_name then
        errorlabstrm "load_physical_library"
          (name_clash_message dir md.md_name f);
      Flags.if_verbose msgnl(str" done]");
      md,table,digest
    with e -> Flags.if_verbose msgnl(str" failed!]"); raise e in
  depgraph := LibraryMap.add md.md_name md.md_deps !depgraph;
  mk_library md f table digest

let get_deps (dir, f) =
  try LibraryMap.find dir !depgraph
  with Not_found ->
    let _ = intern_from_file (dir,f) in
    LibraryMap.find dir !depgraph

(* Read a compiled library and all dependencies, in reverse order.
   Do not include files that are already in the context. *)
let rec intern_library seen (dir, f) needed =
  if LibrarySet.mem dir seen then failwith "Recursive dependencies!";
  (* Look if in the current logical environment *)
  try let _ = find_library dir in needed
  with Not_found ->
  (* Look if already listed and consequently its dependencies too *)
  if List.mem_assoc dir needed then needed
  else
    (* [dir] is an absolute name which matches [f] which must be in loadpath *)
    let m = intern_from_file (dir,f) in
    let seen' = LibrarySet.add dir seen in
    let deps =
      List.map (fun (d,_) -> try_locate_absolute_library d) m.library_deps in
    (dir,m) :: List.fold_right (intern_library seen') deps needed

(* Compute the reflexive transitive dependency closure *)
let rec fold_deps seen ff (dir,f) (s,acc) =
  if LibrarySet.mem dir seen then failwith "Recursive dependencies!";
  if LibrarySet.mem dir s then (s,acc)
  else
    let deps = get_deps (dir,f) in
    let deps = List.map (fun (d,_) -> try_locate_absolute_library d) deps in
    let seen' = LibrarySet.add dir seen in
    let (s',acc') = List.fold_right (fold_deps seen' ff) deps (s,acc) in
    (LibrarySet.add dir s', ff dir acc')

and fold_deps_list seen ff modl needed =
  List.fold_right (fold_deps seen ff) modl needed

let fold_deps_list ff modl acc =
  snd (fold_deps_list LibrarySet.empty ff modl (LibrarySet.empty,acc))

let recheck_library ~norec ~admit ~check =
  let ml = List.map try_locate_qualified_library check in
  let nrl = List.map try_locate_qualified_library norec in
  let al =  List.map try_locate_qualified_library admit in
  let needed = List.rev
    (List.fold_right (intern_library LibrarySet.empty) (ml@nrl) []) in
  (* first compute the closure of norec, remove closure of check,
     add closure of admit, and finally remove norec and check *)
  let nochk = fold_deps_list LibrarySet.add nrl LibrarySet.empty in
  let nochk = fold_deps_list LibrarySet.remove ml nochk in
  let nochk = fold_deps_list LibrarySet.add al nochk in
  (* explicitly required modules cannot be skipped... *)
  let nochk =
    List.fold_right LibrarySet.remove (List.map fst (nrl@ml)) nochk in
  (* *)
  Flags.if_verbose msgnl (fnl()++hv 2 (str "Ordered list:" ++ fnl() ++
    prlist
    (fun (dir,_) -> pr_dirpath dir ++ fnl()) needed));
  List.iter (check_one_lib nochk) needed;
  Flags.if_verbose msgnl(str"Modules were successfully checked")

open Printf

let mem s =
  let m = try_find_library s in
  h 0 (str (sprintf "%dk" (size_kb m)))
