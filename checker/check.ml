(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open Names

let chk_pp = Feedback.msg_notice

let pr_dirpath dp = str (DirPath.to_string dp)
let default_root_prefix = DirPath.empty
let split_dirpath d =
  let l = DirPath.repr d in (DirPath.make (List.tl l), List.hd l)
let extend_dirpath p id = DirPath.make (id :: DirPath.repr p)

type section_path = {
  dirpath : string list ;
  basename : string }

type object_file =
| PhysicalFile of CUnix.physical_path
| LogicalFile of section_path

let dir_of_path p =
  DirPath.make (List.map Id.of_string p.dirpath)
let path_of_dirpath dir =
  match DirPath.repr dir with
      [] -> failwith "path_of_dirpath"
    | l::dir ->
        {dirpath=List.map Id.to_string dir;basename=Id.to_string l}
let pr_dirlist dp =
  prlist_with_sep (fun _ -> str".") str (List.rev dp)
let pr_path sp =
  match sp.dirpath with
      [] -> str sp.basename
    | sl -> pr_dirlist sl ++ str"." ++ str sp.basename

(************************************************************************)

(*s Modules loaded in memory contain the following informations. They are
    kept in the global table [libraries_table]. *)

type compilation_unit_name = DirPath.t

type seg_univ = Univ.ContextSet.t * bool
type seg_proofs = Opaqueproof.opaque_proofterm array

type library_t = {
  library_name : compilation_unit_name;
  library_filename : CUnix.physical_path;
  library_compiled : Safe_typing.compiled_library;
  library_opaques : seg_proofs option;
  library_deps : (compilation_unit_name * Safe_typing.vodigest) array;
  library_digest : Safe_typing.vodigest;
  library_extra_univs : Univ.ContextSet.t }

module LibraryOrdered =
  struct
    type t = DirPath.t
    let compare d1 d2 =
      Pervasives.compare
        (List.rev (DirPath.repr d1)) (List.rev (DirPath.repr d2))
  end

module LibrarySet = Set.Make(LibraryOrdered)
module LibraryMap = Map.Make(LibraryOrdered)

(* This is a map from names to loaded libraries *)
let libraries_table = ref LibraryMap.empty

(* various requests to the tables *)

let find_library dir =
  LibraryMap.find dir !libraries_table

let library_full_filename dir = (find_library dir).library_filename

  (* If a library is loaded several time, then the first occurrence must
     be performed first, thus the libraries_loaded_list ... *)

let register_loaded_library m =
  libraries_table := LibraryMap.add m.library_name m !libraries_table

(* Map from library names to table of opaque terms *)
let opaque_tables = ref LibraryMap.empty

let access_opaque_table dp i =
  let t =
    try LibraryMap.find dp !opaque_tables
    with Not_found -> assert false
  in
  assert (i < Array.length t);
  t.(i)

let access_discharge = Cooking.cook_constr

let indirect_accessor = {
  Opaqueproof.access_proof = access_opaque_table;
  Opaqueproof.access_discharge = access_discharge;
}

let () = Mod_checking.set_indirect_accessor indirect_accessor

let check_one_lib admit senv (dir,m) =
  let md = m.library_compiled in
  let dig = m.library_digest in
  (* Look up if the library is to be admitted correct. We could
     also check if it carries a validation certificate (yet to
     be implemented). *)
  let senv =
    if LibrarySet.mem dir admit then
      (Flags.if_verbose Feedback.msg_notice
         (str "Admitting library: " ++ pr_dirpath dir);
       Safe_checking.unsafe_import senv md m.library_extra_univs dig)
    else
      (Flags.if_verbose Feedback.msg_notice
         (str "Checking library: " ++ pr_dirpath dir);
       Safe_checking.import senv md m.library_extra_univs dig)
  in
    register_loaded_library m; senv

(*************************************************************************)
(*s Load path. Mapping from physical to logical paths etc.*)

type logical_path = DirPath.t

let load_paths = ref ([],[] : CUnix.physical_path list * logical_path list)


let find_logical_path phys_dir =
  let phys_dir = CUnix.canonical_path_name phys_dir in
  let physical, logical = !load_paths in
  match List.filter2 (fun p d -> p = phys_dir) physical logical with
  | _,[dir] -> dir
  | _,[] -> default_root_prefix
  | _,l -> anomaly (Pp.str ("Two logical paths are associated to "^phys_dir^"."))

let remove_load_path dir =
  let physical, logical = !load_paths in
  load_paths := List.filter2 (fun p d -> p <> dir) physical logical

let add_load_path (phys_path,coq_path) =
  if !Flags.debug then
    Feedback.msg_notice (str "path: " ++ pr_dirpath coq_path ++ str " ->" ++ spc() ++
           str phys_path);
  let phys_path = CUnix.canonical_path_name phys_path in
  let physical, logical = !load_paths in
    match List.filter2 (fun p d -> p = phys_path) physical logical with
      | _,[dir] ->
	  if coq_path <> dir
            (* If this is not the default -I . to coqtop *)
            && not
            (phys_path = CUnix.canonical_path_name Filename.current_dir_name
		&& coq_path = default_root_prefix)
	  then
	    begin
              (* Assume the user is concerned by library naming *)
	      if dir <> default_root_prefix then
		Feedback.msg_warning
		  (str phys_path ++ strbrk " was previously bound to " ++
		   pr_dirpath dir ++ strbrk "; it is remapped to " ++
		   pr_dirpath coq_path);
	      remove_load_path phys_path;
	      load_paths := (phys_path::fst !load_paths, coq_path::snd !load_paths)
	    end
      | _,[] ->
	  load_paths := (phys_path :: fst !load_paths, coq_path :: snd !load_paths)
      | _ -> anomaly (Pp.str ("Two logical paths are associated to "^phys_path^"."))

let load_paths_of_dir_path dir =
  let physical, logical = !load_paths in
  fst (List.filter2 (fun p d -> d = dir) physical logical)

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
    let name = Id.to_string base^".vo" in
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
    (* we assume qid is an absolute dirpath *)
    let loadpath = load_paths_of_dir_path (dir_of_path qid) in
    if loadpath = [] then raise LibUnmappedDir;
    let name =  qid.basename^".vo" in
    let path, file = System.where_in_path loadpath name in
    let dir =
      extend_dirpath (find_logical_path path) (Id.of_string qid.basename) in
    (* Look if loaded *)
    try
      (dir, library_full_filename dir)
    with Not_found ->
      (dir, file)
  with Not_found -> raise LibNotFound

let error_unmapped_dir qid =
  let prefix = qid.dirpath in
  user_err ~hdr:"load_absolute_library_from"
    (str "Cannot load " ++ pr_path qid ++ str ":" ++ spc () ++
     str "no physical path bound to" ++ spc () ++ pr_dirlist prefix ++ fnl ())

let error_lib_not_found qid =
  user_err ~hdr:"load_absolute_library_from"
    (str"Cannot find library " ++ pr_path qid ++ str" in loadpath")

let try_locate_absolute_library dir =
  try
    locate_absolute_library dir
  with
    | LibUnmappedDir -> error_unmapped_dir (path_of_dirpath dir)
    | LibNotFound -> error_lib_not_found (path_of_dirpath dir)

let try_locate_qualified_library lib = match lib with
| PhysicalFile f ->
  let () =
    if not (System.file_exists_respecting_case "" f) then
      error_lib_not_found { dirpath = []; basename = f; }
  in
  let dir = Filename.dirname f in
  let base = Filename.chop_extension (Filename.basename f) in
  let dir = extend_dirpath (find_logical_path dir) (Id.of_string base) in
  (dir, f)
| LogicalFile qid ->
  try
    locate_qualified_library qid
  with
    | LibUnmappedDir -> error_unmapped_dir qid
    | LibNotFound -> error_lib_not_found qid

(************************************************************************)
(*s Low-level interning of libraries from files *)

let raw_intern_library f =
  System.raw_intern_state Coq_config.vo_magic_number f

(************************************************************************)
(* Internalise libraries *)

type summary_disk = {
  md_name : compilation_unit_name;
  md_imports : compilation_unit_name array;
  md_deps : (compilation_unit_name * Safe_typing.vodigest) array;
}

module Dyn = Dyn.Make ()
type obj = Dyn.t (* persistent dynamic objects *)
type lib_objects = (Id.t * obj) list
type library_objects = lib_objects * lib_objects

type library_disk = {
  md_compiled : Safe_typing.compiled_library;
  md_objects : library_objects;
}

let mk_library sd md f table digest cst = {
  library_name = sd.md_name;
  library_filename = f;
  library_compiled = md.md_compiled;
  library_opaques = table;
  library_deps = sd.md_deps;
  library_digest = digest;
  library_extra_univs = cst }

let name_clash_message dir mdir f =
  str ("The file " ^ f ^ " contains library") ++ spc () ++
  pr_dirpath mdir ++ spc () ++ str "and not library" ++ spc() ++
  pr_dirpath dir

type intern_mode = Rec | Root | Dep (* Rec = standard, Root = -norec, Dep = dependency of norec *)

(* Dependency graph *)
let depgraph = ref LibraryMap.empty

let marshal_in_segment f ch =
  try
    let stop = input_binary_int ch in
    let v = Analyze.instantiate (Analyze.parse_channel ch) in
    let digest = Digest.input ch in
    Obj.obj v, stop, digest
  with _ ->
    user_err (str "Corrupted file " ++ quote (str f))

let skip_in_segment f ch =
  try
    let stop = (input_binary_int ch : int) in
    seek_in ch stop;
    let digest = Digest.input ch in
    stop, digest
  with _ ->
    user_err (str "Corrupted file " ++ quote (str f))

let marshal_or_skip ~intern_mode f ch =
  if intern_mode <> Dep then
    let v, pos, digest = marshal_in_segment f ch in
    Some v, pos, digest
  else
    let pos, digest = skip_in_segment f ch in
    None, pos, digest

let intern_from_file ~intern_mode (dir, f) =
  let validate a b c = if intern_mode <> Dep then Validate.validate a b c in
  Flags.if_verbose chk_pp (str"[intern "++str f++str" ...");
  let (sd,md,table,opaque_csts,digest) =
    try
      let marshal_in_segment f ch = if intern_mode <> Dep
        then marshal_in_segment f ch
        else System.marshal_in_segment f ch
      in
      let ch = System.with_magic_number_check raw_intern_library f in
      let (sd:summary_disk), _, digest = marshal_in_segment f ch in
      let (md:library_disk), _, digest = marshal_in_segment f ch in
      let (opaque_csts:seg_univ option), _, udg = marshal_in_segment f ch in
      let (tasks:'a option), _, _ = marshal_in_segment f ch in
      let (table:seg_proofs option), pos, checksum =
        marshal_or_skip ~intern_mode f ch in
      (* Verification of the final checksum *)
      let () = close_in ch in
      let ch = open_in_bin f in
      if not (String.equal (Digest.channel ch pos) checksum) then
        user_err ~hdr:"intern_from_file" (str "Checksum mismatch");
      let () = close_in ch in
      if dir <> sd.md_name then
        user_err ~hdr:"intern_from_file"
          (name_clash_message dir sd.md_name f);
      if tasks <> None then
        user_err ~hdr:"intern_from_file"
          (str "The file "++str f++str " contains unfinished tasks");
      if opaque_csts <> None then begin
       Flags.if_verbose chk_pp (str " (was a vio file) ");
      Option.iter (fun (_,b) -> if not b then
        user_err ~hdr:"intern_from_file"
          (str "The file "++str f++str " is still a .vio"))
        opaque_csts;
      validate !Flags.debug Values.v_univopaques opaque_csts;
      end;
      (* Verification of the unmarshalled values *)
      validate !Flags.debug Values.v_libsum sd;
      validate !Flags.debug Values.v_lib md;
      validate !Flags.debug Values.(Opt v_opaques) table;
      Flags.if_verbose chk_pp (str" done]" ++ fnl ());
      let digest =
        if opaque_csts <> None then Safe_typing.Dvivo (digest,udg)
        else (Safe_typing.Dvo_or_vi digest) in
      sd,md,table,opaque_csts,digest
    with e -> Flags.if_verbose chk_pp (str" failed!]" ++ fnl ()); raise e in
  depgraph := LibraryMap.add sd.md_name sd.md_deps !depgraph;
  Option.iter (fun table -> opaque_tables := LibraryMap.add sd.md_name table !opaque_tables) table;
  let extra_cst =
    Option.default Univ.ContextSet.empty
      (Option.map (fun (cs,_) -> cs) opaque_csts) in
  mk_library sd md f table digest extra_cst

let get_deps (dir, f) =
  try LibraryMap.find dir !depgraph
  with Not_found ->
    let _ = intern_from_file (dir,f) in
    LibraryMap.find dir !depgraph

(* Read a compiled library and all dependencies, in reverse order.
   Do not include files that are already in the context. *)
let rec intern_library ~intern_mode seen (dir, f) needed =
  if LibrarySet.mem dir seen then failwith "Recursive dependencies!";
  (* Look if in the current logical environment *)
  try let _ = find_library dir in needed
  with Not_found ->
  (* Look if already listed and consequently its dependencies too *)
  if List.mem_assoc_f DirPath.equal dir needed then needed
  else
    (* [dir] is an absolute name which matches [f] which must be in loadpath *)
    let m = intern_from_file ~intern_mode (dir,f) in
    let seen' = LibrarySet.add dir seen in
    let deps =
      Array.map (fun (d,_) -> try_locate_absolute_library d) m.library_deps
    in
    let intern_mode = match intern_mode with Rec -> Rec | Root | Dep -> Dep in
    (dir,m) :: Array.fold_right (intern_library ~intern_mode seen') deps needed

(* Compute the reflexive transitive dependency closure *)
let rec fold_deps seen ff (dir,f) (s,acc) =
  if LibrarySet.mem dir seen then failwith "Recursive dependencies!";
  if LibrarySet.mem dir s then (s,acc)
  else
    let deps = get_deps (dir,f) in
    let deps = Array.map (fun (d,_) -> try_locate_absolute_library d) deps in
    let seen' = LibrarySet.add dir seen in
    let (s',acc') = Array.fold_right (fold_deps seen' ff) deps (s,acc) in
    (LibrarySet.add dir s', ff dir acc')

and fold_deps_list seen ff modl needed =
  List.fold_right (fold_deps seen ff) modl needed

let fold_deps_list ff modl acc =
  snd (fold_deps_list LibrarySet.empty ff modl (LibrarySet.empty,acc))

let recheck_library senv ~norec ~admit ~check =
  let ml = List.map try_locate_qualified_library check in
  let nrl = List.map try_locate_qualified_library norec in
  let al =  List.map try_locate_qualified_library admit in
  let needed = List.fold_right (intern_library ~intern_mode:Rec LibrarySet.empty) ml [] in
  let needed = List.fold_right (intern_library ~intern_mode:Root LibrarySet.empty) nrl needed in
  let needed = List.rev needed in
  (* first compute the closure of norec, remove closure of check,
     add closure of admit, and finally remove norec and check *)
  let nochk = fold_deps_list LibrarySet.add nrl LibrarySet.empty in
  let nochk = fold_deps_list LibrarySet.remove ml nochk in
  let nochk = fold_deps_list LibrarySet.add al nochk in
  (* explicitly required modules cannot be skipped... *)
  let nochk =
    List.fold_right LibrarySet.remove (List.map fst (nrl@ml)) nochk in
  (* *)
  Flags.if_verbose Feedback.msg_notice (fnl()++hv 2 (str "Ordered list:" ++ fnl() ++
    prlist
    (fun (dir,_) -> pr_dirpath dir ++ fnl()) needed));
  let senv = List.fold_left (check_one_lib nochk) senv needed in
  Flags.if_verbose Feedback.msg_notice (str"Modules were successfully checked");
  senv
