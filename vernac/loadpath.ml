(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
module DP = Names.DirPath

(** Load paths. Mapping from physical to logical paths. *)

type t = {
  path_physical : CUnix.physical_path;
  path_logical : DP.t;
  path_implicit : bool;
}

let load_paths = Summary.ref ([] : t list) ~name:"LOADPATHS"

let logical p = p.path_logical
let physical p = p.path_physical

let pp p =
  let dir = DP.print p.path_logical in
  let path = Pp.str (CUnix.escaped_string_of_physical_path p.path_physical) in
  Pp.(hov 2 (dir ++ spc () ++ path))

let get_load_paths () = !load_paths

let anomaly_too_many_paths path =
  CErrors.anomaly Pp.(str "Several logical paths are associated to" ++ spc () ++ str path ++ str ".")

let find_load_path phys_dir =
  let phys_dir = CUnix.canonical_path_name phys_dir in
  let filter p = String.equal p.path_physical phys_dir in
  let paths = List.filter filter !load_paths in
  match paths with
  | [] -> raise Not_found
  | [p] -> p
  | _ -> anomaly_too_many_paths phys_dir

let remove_load_path dir =
  let filter p = not (String.equal p.path_physical dir) in
  load_paths := List.filter filter !load_paths

let warn_overriding_logical_loadpath =
  CWarnings.create ~name:"overriding-logical-loadpath" ~category:"loadpath"
    (fun (phys_path, old_path, coq_path) ->
       Pp.(seq [str phys_path; strbrk " was previously bound to "
               ; DP.print old_path; strbrk "; it is remapped to "
               ; DP.print coq_path]))

let add_load_path phys_path coq_path ~implicit =
  let phys_path = CUnix.canonical_path_name phys_path in
  let filter p = String.equal p.path_physical phys_path in
  let binding = {
    path_logical = coq_path;
    path_physical = phys_path;
    path_implicit = implicit;
  } in
  match List.filter filter !load_paths with
  | [] ->
    load_paths := binding :: !load_paths
  | [{ path_logical = old_path; path_implicit = old_implicit }] ->
    let replace =
      if DP.equal coq_path old_path then
        implicit <> old_implicit
      else
        let () =
          (* Do not warn when overriding the default "-I ." path *)
          if not (DP.equal old_path Libnames.default_root_prefix) then
          warn_overriding_logical_loadpath (phys_path, old_path, coq_path)
        in
        true in
    if replace then
      begin
        remove_load_path phys_path;
        load_paths := binding :: !load_paths;
      end
  | _ -> anomaly_too_many_paths phys_path

let filter_path f =
  let rec aux = function
  | [] -> []
  | p :: l ->
    if f p.path_logical then (p.path_physical, p.path_logical) :: aux l
    else aux l
  in
  aux !load_paths

let expand_path ?root dir =
  let rec aux = function
  | [] -> []
  | { path_physical = ph; path_logical = lg; path_implicit = implicit } :: l ->
    let success =
      match root with
      | None ->
        if implicit then Libnames.is_dirpath_suffix_of dir lg
        else DP.equal dir lg
      | Some root ->
        Libnames.(is_dirpath_prefix_of root lg &&
                  is_dirpath_suffix_of dir (drop_dirpath_prefix root lg)) in
    if success then (ph, lg) :: aux l else aux l in
  aux !load_paths

let locate_file fname =
  let paths = List.map physical !load_paths in
  let _,longfname =
    System.find_file_in_path ~warn:(not !Flags.quiet) paths fname in
  longfname

(************************************************************************)
(*s Locate absolute or partially qualified library names in the path *)

type library_location = LibLoaded | LibInPath
type locate_error = LibUnmappedDir | LibNotFound
type 'a locate_result = ('a, locate_error) result

let warn_several_object_files =
  CWarnings.create ~name:"several-object-files" ~category:"require"
    Pp.(fun (vi, vo) ->
        seq [ str "Loading"; spc (); str vi
            ; strbrk " instead of "; str vo
            ; strbrk " because it is more recent"
            ])


let select_vo_file ~warn loadpath base =
  let find ext =
    let loadpath = List.map fst loadpath in
    try
      let name = Names.Id.to_string base ^ ext in
      let lpath, file =
        System.where_in_path ~warn loadpath name in
      Some (lpath, file)
    with Not_found -> None in
  match find ".vo", find ".vio" with
  | None, None ->
    Error LibNotFound
  | Some res, None | None, Some res ->
    Ok res
  | Some (_, vo), Some (_, vi as resvi)
    when Unix.((stat vo).st_mtime < (stat vi).st_mtime) ->
    warn_several_object_files (vi, vo);
    Ok resvi
  | Some resvo, Some _ ->
    Ok resvo

let locate_absolute_library dir : CUnix.physical_path locate_result =
  (* Search in loadpath *)
  let pref, base = Libnames.split_dirpath dir in
  let loadpath = filter_path (fun dir -> DP.equal dir pref) in
  match loadpath with
  | [] -> Error LibUnmappedDir
  | _ ->
    match select_vo_file ~warn:false loadpath base with
    | Ok (_, file) -> Ok file
    | Error fail -> Error fail

let locate_qualified_library ?root ?(warn = true) qid :
  (library_location * DP.t * CUnix.physical_path) locate_result =
  (* Search library in loadpath *)
  let dir, base = Libnames.repr_qualid qid in
  let loadpath = expand_path ?root dir in
  match loadpath with
  | [] -> Error LibUnmappedDir
  | _ ->
    match select_vo_file ~warn loadpath base with
    | Ok (lpath, file) ->
      let dir = Libnames.add_dirpath_suffix
          (CString.List.assoc lpath loadpath) base in
      (* Look if loaded *)
      if Library.library_is_loaded dir
      then Ok (LibLoaded, dir, Library.library_full_filename dir)
      (* Otherwise, look for it in the file system *)
      else Ok (LibInPath, dir, file)
    | Error fail -> Error fail

let error_unmapped_dir qid =
  let prefix, _ = Libnames.repr_qualid qid in
  CErrors.user_err ~hdr:"load_absolute_library_from"
    Pp.(seq [ str "Cannot load "; Libnames.pr_qualid qid; str ":"; spc ()
            ; str "no physical path bound to"; spc ()
            ; DP.print prefix; fnl ()
            ])

let error_lib_not_found qid =
  CErrors.user_err ~hdr:"load_absolute_library_from"
    Pp.(seq [ str "Cannot find library "; Libnames.pr_qualid qid; str" in loadpath"])

let try_locate_absolute_library dir =
  match locate_absolute_library dir with
  | Ok res -> res
  | Error LibUnmappedDir ->
    error_unmapped_dir (Libnames.qualid_of_dirpath dir)
  | Error LibNotFound ->
    error_lib_not_found (Libnames.qualid_of_dirpath dir)

(** { 5 Extending the load path } *)

(* Adds a path to the Coq and ML paths *)
type add_ml = AddNoML | AddTopML | AddRecML

type vo_path_spec = {
  unix_path : string;  (* Filesystem path containing vo/ml files *)
  coq_path  : DP.t;    (* Coq prefix for the path *)
  implicit  : bool;    (* [implicit = true] avoids having to qualify with [coq_path] *)
  has_ml    : add_ml;  (* If [has_ml] is true, the directory will also be search for plugins *)
}

type coq_path_spec =
  | VoPath of vo_path_spec
  | MlPath of string

type coq_path = {
  path_spec: coq_path_spec;
  recursive: bool;
}

let warn_cannot_open_path =
  CWarnings.create ~name:"cannot-open-path" ~category:"filesystem"
    (fun unix_path -> Pp.(str "Cannot open " ++ str unix_path))

let warn_cannot_use_directory =
  CWarnings.create ~name:"cannot-use-directory" ~category:"filesystem"
    (fun d ->
       Pp.(str "Directory " ++ str d ++
           strbrk " cannot be used as a Coq identifier (skipped)"))

let convert_string d =
  try Names.Id.of_string d
  with
  | CErrors.UserError _ ->
    let d = Unicode.escaped_if_non_utf8 d in
    warn_cannot_use_directory d;
    raise Exit

let add_vo_path ~recursive lp =
  let unix_path = lp.unix_path in
  let implicit = lp.implicit in
  if System.exists_dir unix_path then
    let dirs = if recursive then System.all_subdirs ~unix_path else [] in
    let prefix = DP.repr lp.coq_path in
    let convert_dirs (lp, cp) =
      try
        let path = List.rev_map convert_string cp @ prefix in
        Some (lp, DP.make path)
      with Exit -> None
    in
    let dirs = List.map_filter convert_dirs dirs in
    let add_ml_dir = Mltop.add_ml_dir ~recursive:false in
    let () = match lp.has_ml with
      | AddNoML -> ()
      | AddTopML ->
        Mltop.add_ml_dir ~recursive:false unix_path
      | AddRecML ->
        List.iter (fun (lp,_) -> add_ml_dir lp) dirs;
        add_ml_dir unix_path in
    let add (path, dir) = add_load_path path ~implicit dir in
    let () = List.iter add dirs in
    add_load_path unix_path ~implicit lp.coq_path
  else
    warn_cannot_open_path unix_path

let add_coq_path { recursive; path_spec } = match path_spec with
  | VoPath lp ->
    add_vo_path ~recursive lp
  | MlPath dir ->
    Mltop.add_ml_dir ~recursive dir
