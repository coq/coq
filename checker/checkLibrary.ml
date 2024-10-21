(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
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

type seg_proofs = Opaqueproof.opaque_proofterm option array

type library_t = {
  library_name : compilation_unit_name;
  library_filename : CUnix.physical_path;
  library_compiled : Safe_typing.compiled_library;
  library_opaques : seg_proofs;
  library_deps : (compilation_unit_name * Safe_typing.vodigest) array;
  library_digest : Safe_typing.vodigest;
  library_vm : Vmlibrary.on_disk;
}

module LibraryOrdered =
  struct
    type t = DirPath.t
    let compare d1 d2 =
      compare
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
  let i = Opaqueproof.repr_handle i in
  let () = assert (0 <= i && i < Array.length t) in
  t.(i)

let indirect_accessor o =
  let (sub, ci, dp, i) = Opaqueproof.repr o in
  let c = access_opaque_table dp i in
  let c = match c with
  | None ->  CErrors.user_err Pp.(str "Cannot access opaque delayed proof.")
  | Some c -> c
  in
  let (c, prv) = Discharge.cook_opaque_proofterm ci c in
  let c = Mod_subst.subst_mps_list sub c in
  (c, prv)

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
       Safe_checking.unsafe_import (fst senv) md m.library_vm dig),
      (snd senv)
    else
      (Flags.if_verbose Feedback.msg_notice
         (str "Checking library: " ++ pr_dirpath dir);
       Safe_checking.import (fst senv) (snd senv) md m.library_vm dig)
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
  | _,l -> CErrors.anomaly (Pp.str ("Two logical paths are associated to "^phys_dir^"."))

let remove_load_path dir =
  let physical, logical = !load_paths in
  load_paths := List.filter2 (fun p d -> p <> dir) physical logical

let add_load_path (phys_path,rocq_path) =
  if CDebug.(get_flag misc) then
    Feedback.msg_notice (str "path: " ++ pr_dirpath rocq_path ++ str " ->" ++ spc() ++
           str phys_path);
  let phys_path = CUnix.canonical_path_name phys_path in
  let physical, logical = !load_paths in
    match List.filter2 (fun p d -> p = phys_path) physical logical with
      | _,[dir] ->
          if rocq_path <> dir
            (* If this is not the default -I . to coqtop *)
            && not
            (phys_path = CUnix.canonical_path_name Filename.current_dir_name
                && rocq_path = default_root_prefix)
          then
            begin
              (* Assume the user is concerned by library naming *)
              if dir <> default_root_prefix then
                Feedback.msg_warning
                  (str phys_path ++ strbrk " was previously bound to " ++
                   pr_dirpath dir ++ strbrk "; it is remapped to " ++
                   pr_dirpath rocq_path);
              remove_load_path phys_path;
              load_paths := (phys_path::fst !load_paths, rocq_path::snd !load_paths)
            end
      | _,[] ->
          load_paths := (phys_path :: fst !load_paths, rocq_path :: snd !load_paths)
      | _ -> CErrors.anomaly (Pp.str ("Two logical paths are associated to "^phys_path^"."))

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
  CErrors.user_err
    (str "Cannot load " ++ pr_path qid ++ str ":" ++ spc () ++
     str "no physical path bound to" ++ spc () ++ pr_dirlist prefix
     ++ str "." ++ fnl ())

let error_lib_not_found qid =
  CErrors.user_err
    (str "Cannot find library " ++ pr_path qid ++ str " in loadpath.")

let try_locate_absolute_library dir =
  try
    locate_absolute_library dir
  with
    | LibUnmappedDir -> error_unmapped_dir (path_of_dirpath dir)
    | LibNotFound -> error_lib_not_found (path_of_dirpath dir)

let try_locate_qualified_library lib = match lib with
| PhysicalFile f ->
  let () =
    if not (Sys.file_exists f) then
      CErrors.user_err Pp.(str f ++ str ": file not found.")
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

let lib_to_string = function
  | PhysicalFile f -> f
  | LogicalFile qid -> String.concat "." (List.rev (qid.basename :: qid.dirpath))

let try_locate_qualified_library lib : _ * _ =
  NewProfile.profile "try_locate_qualified_library"
    ~args:(fun () -> [("name", `String (lib_to_string lib))])
    (fun () -> try_locate_qualified_library lib)
    ()

(************************************************************************)
(*s Low-level interning of libraries from files *)

let raw_intern_library f =
  ObjFile.open_in ~file:f

(************************************************************************)
(* Internalise libraries *)

type library_info

type summary_disk = {
  md_name : compilation_unit_name;
  md_deps : (compilation_unit_name * Safe_typing.vodigest) array;
  md_ocaml : string;
  md_info : library_info;
}

type library_objects

type library_disk = {
  md_compiled : Safe_typing.compiled_library;
  md_syntax_objects : library_objects;
  md_objects : library_objects;
}

let mk_library sd md f table digest vm = {
  library_name = sd.md_name;
  library_filename = f;
  library_compiled = md.md_compiled;
  library_opaques = table;
  library_deps = sd.md_deps;
  library_digest = digest;
  library_vm = vm;
}

let name_clash_message dir mdir f =
  str ("The file " ^ f ^ " contains library") ++ spc () ++
  pr_dirpath mdir ++ spc () ++ str "and not library" ++ spc() ++
  pr_dirpath dir

type intern_mode = Rec | Root | Dep (* Rec = standard, Root = -norec, Dep = dependency of norec *)

(* Dependency graph *)
let depgraph = ref LibraryMap.empty

let marshal_in_segment (type a) ~validate ~value ~(segment : a ObjFile.segment) f ch : a =
  NewProfile.profile "marshal_in_segment" (fun () ->
  let () = LargeFile.seek_in ch segment.ObjFile.pos in
  if validate then
    let v =
      try
        let v = Analyze.parse_channel ch in
        let digest = Digest.input ch in
        let () = if not (String.equal digest segment.ObjFile.hash) then raise_notrace Exit in
        v
      with exn when CErrors.noncritical exn ->
        CErrors.user_err (str "Corrupted file " ++ quote (str f))
    in
    let () = Validate.validate value v in
    let v = Analyze.instantiate v in
    Obj.obj v
  else
    System.marshal_in f ch)
    ()

let summary_seg : summary_disk ObjFile.id = ObjFile.make_id "summary"
let library_seg : library_disk ObjFile.id = ObjFile.make_id "library"
let opaques_seg : seg_proofs ObjFile.id = ObjFile.make_id "opaques"
let vm_seg = Vmlibrary.vm_segment

let intern_from_file ~intern_mode ~enable_VM (dir, f) =
  let validate = intern_mode <> Dep in
  Flags.if_verbose chk_pp (str"[intern "++str f++str" ...");
  let (sd,md,table,vmlib,digest) =
    try
      (* First pass to read the metadata of the file *)
      let ch = System.with_magic_number_check raw_intern_library f in
      let seg_sd = ObjFile.get_segment ch ~segment:summary_seg in
      let seg_md = ObjFile.get_segment ch ~segment:library_seg in
      let seg_opaque = ObjFile.get_segment ch ~segment:opaques_seg in
      let seg_vmlib = ObjFile.get_segment ch ~segment:vm_seg in
      let () = ObjFile.close_in ch in
      (* Actually read the data *)
      let ch = open_in_bin f in

      let sd = marshal_in_segment ~validate ~value:Values.v_libsum ~segment:seg_sd f ch in
      let md = marshal_in_segment ~validate ~value:Values.v_lib ~segment:seg_md f ch in
      let table = marshal_in_segment ~validate ~value:Values.v_opaquetable ~segment:seg_opaque f ch in
      let vmlib = if enable_VM
        then marshal_in_segment ~validate ~value:Values.v_vmlib ~segment:seg_vmlib f ch
        else Vmlibrary.(export (set_path dir empty))
      in
      (* Verification of the final checksum *)
      let () = close_in ch in
      let () = System.check_caml_version ~caml:sd.md_ocaml ~file:f in
      if dir <> sd.md_name then
        CErrors.user_err
          (name_clash_message dir sd.md_name f);
      Flags.if_verbose chk_pp (str" done]" ++ fnl ());
      let digest =
        Safe_typing.Dvo_or_vi seg_md.hash in
      sd,md,table,vmlib,digest
    with e -> Flags.if_verbose chk_pp (str" failed!]" ++ fnl ()); raise e in
  depgraph := LibraryMap.add sd.md_name sd.md_deps !depgraph;
  opaque_tables := LibraryMap.add sd.md_name table !opaque_tables;
  mk_library sd md f table digest (Vmlibrary.inject vmlib)

let intern_from_file ~intern_mode ~enable_VM dirf : library_t =
  NewProfile.profile "intern_from_file"
    ~args:(fun () -> [("name", `String (DirPath.to_string (fst dirf)))])
    (fun () -> intern_from_file ~intern_mode ~enable_VM dirf)
    ()

(* Read a compiled library and all dependencies, in reverse order.
   Do not include files that are already in the context. *)
let rec intern_library ~intern_mode ~enable_VM seen (dir, f) needed =
  if LibrarySet.mem dir seen then failwith "Recursive dependencies!";
  (* Look if in the current logical environment *)
  try let _ = find_library dir in needed
  with Not_found ->
  (* Look if already listed and consequently its dependencies too *)
  if List.mem_assoc_f DirPath.equal dir needed then needed
  else
    (* [dir] is an absolute name which matches [f] which must be in loadpath *)
    let m = intern_from_file ~intern_mode ~enable_VM (dir,f) in
    let seen' = LibrarySet.add dir seen in
    let deps =
      Array.map (fun (d,_) -> try_locate_absolute_library d) m.library_deps
    in
    let intern_mode = match intern_mode with Rec -> Rec | Root | Dep -> Dep in
    (dir,m) :: Array.fold_right (intern_library ~intern_mode ~enable_VM seen') deps needed

(* Compute the reflexive transitive dependency closure *)
let rec fold_deps seen ff (dir,f) (s,acc) =
  if LibrarySet.mem dir seen then failwith "Recursive dependencies!";
  if LibrarySet.mem dir s then (s,acc)
  else
    let deps = match LibraryMap.find_opt dir !depgraph with
      | Some deps -> deps
      | None ->
        CErrors.anomaly Pp.(str "missing dep when computing closure (" ++ DirPath.print dir ++ str ")")
    in
    let deps = Array.map (fun (d,_) -> try_locate_absolute_library d) deps in
    let seen' = LibrarySet.add dir seen in
    let (s',acc') = Array.fold_right (fold_deps seen' ff) deps (s,acc) in
    (LibrarySet.add dir s', ff dir acc')

and fold_deps_list seen ff modl needed =
  List.fold_right (fold_deps seen ff) modl needed

let fold_deps_list ff modl acc =
  snd (fold_deps_list LibrarySet.empty ff modl (LibrarySet.empty,acc))

let recheck_library senv ~norec ~admit ~check =
  let enable_VM = (Environ.typing_flags (Safe_typing.env_of_safe_env senv)).enable_VM in
  let ml = List.map try_locate_qualified_library check in
  let nrl = List.map try_locate_qualified_library norec in
  let al =  List.map try_locate_qualified_library admit in
  let needed = List.fold_right (intern_library ~intern_mode:Rec ~enable_VM LibrarySet.empty) ml [] in
  let needed = List.fold_right (intern_library ~intern_mode:Root ~enable_VM LibrarySet.empty) nrl needed in
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
  let senv = List.fold_left (check_one_lib nochk) (senv, Cmap.empty) needed in
  Flags.if_verbose Feedback.msg_notice (str"Modules were successfully checked");
  senv
