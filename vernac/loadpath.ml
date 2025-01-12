(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
  path_implicit : bool;  (* true for -R, false for -Q in command line *)
  path_root : (CUnix.physical_path * DP.t);
}

let load_paths = Summary.ref ([] : t list) ~stage:Summary.Stage.Synterp ~name:"LOADPATHS"

let logical p = p.path_logical
let physical p = p.path_physical

let pp p =
  let dir = DP.print p.path_logical in
  let path = Pp.str (CUnix.escaped_string_of_physical_path p.path_physical) in
  Pp.(hov 2 (dir ++ spc () ++ path))

let get_load_paths () = !load_paths

let anomaly_too_many_paths path =
  CErrors.anomaly Pp.(str "Several logical paths are associated with" ++ spc () ++ str path ++ str ".")

let find_load_path phys_dir =
  let phys_dir = CUnix.canonical_path_name phys_dir in
  let filter p = String.equal p.path_physical phys_dir in
  let paths = List.filter filter !load_paths in
  match paths with
  | [] -> raise Not_found
  | [p] -> p
  | _ -> anomaly_too_many_paths phys_dir

(* get the list of load paths that correspond to a given logical path *)
let find_with_logical_path dirpath =
  List.filter (fun p -> Names.DirPath.equal p.path_logical dirpath) !load_paths

let warn_file_found_multiple_times =
  CWarnings.create ~name:"ambiguous-extra-dep" ~category:CWarnings.CoreCategories.filesystem
    (fun (file,from,other,extra) ->
      Pp.(str "File " ++ str file ++ str " found twice in " ++
      Names.DirPath.print from ++ str":" ++ spc () ++ str other ++ str " (selected)," ++
      spc() ++ str extra ++ str ".") )

let rec first_path_containing ?loc from file acc = function
  | [] ->
      begin match acc with
      | Some x -> x
      | None ->
        CErrors.user_err Pp.(str "File " ++ str file ++ str " not found in " ++
        Names.DirPath.print from ++ str".")
     end
  | x :: xs ->
      let abspath = x ^ "/" ^ file in
      if Sys.file_exists abspath then begin
        match acc with
        | None -> first_path_containing ?loc from file (Some abspath) xs
        | Some other ->
            warn_file_found_multiple_times ?loc (file,from,other,abspath);
            first_path_containing ?loc from file acc xs
      end else
        first_path_containing ?loc from file acc xs

let find_extra_dep_with_logical_path ?loc ~from ~file () =
  match find_with_logical_path from with
  | _ :: _ as paths ->
    let paths = List.map physical paths in
    first_path_containing ?loc from file None paths
  | [] -> CErrors.user_err
      Pp.(str "No LoadPath found for " ++ Names.DirPath.print from ++ str".")


let remove_load_path dir =
  let filter p = not (String.equal p.path_physical dir) in
  load_paths := List.filter filter !load_paths

let warn_overriding_logical_loadpath =
  CWarnings.create ~name:"overriding-logical-loadpath" ~category:CWarnings.CoreCategories.filesystem
    (fun (phys_path, old_path, rocq_path) ->
       Pp.(seq [str phys_path; strbrk " was previously bound to "
               ; DP.print old_path; strbrk "; it is remapped to "
               ; DP.print rocq_path]))

let add_load_path root phys_path rocq_path ~implicit =
  let phys_path = CUnix.canonical_path_name phys_path in
  let filter p = String.equal p.path_physical phys_path in
  let binding = {
    path_logical = rocq_path;
    path_physical = phys_path;
    path_implicit = implicit;
    path_root = root;
  } in
  match List.filter filter !load_paths with
  | [] ->
    load_paths := binding :: !load_paths
  | [{ path_logical = old_path; path_implicit = old_implicit }] ->
    let replace =
      if DP.equal rocq_path old_path then
        implicit <> old_implicit
      else
        let () =
          (* Do not warn when overriding the default "-I ." path *)
          if not (DP.equal old_path Libnames.default_root_prefix) then
          warn_overriding_logical_loadpath (phys_path, old_path, rocq_path)
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

let eq_root (phys,log_path) (phys',log_path') =
  String.equal phys phys' && Names.DirPath.equal log_path log_path'

let add_path root file = function
  | [] -> [root,[file]]
  | (root',l) :: l' as l'' -> if eq_root root root' then (root', file::l) :: l' else (root,[file]) :: l''

let expand_path ?root dir =
  let exact_path = match root with None -> dir | Some root -> Libnames.append_dirpath root dir in
  let rec aux = function
  | [] -> [], []
  | { path_physical = ph; path_logical = lg; path_implicit = implicit; path_root } :: l ->
    let full, others = aux l in
    if DP.equal exact_path lg then
      (* Most recent full match comes first *)
      (ph, lg) :: full, others
    else
    let success =
      match root with
      | None -> implicit && Libnames.is_dirpath_suffix_of dir lg
      | Some root ->
        Libnames.(is_dirpath_prefix_of root lg &&
                  is_dirpath_suffix_of dir (drop_dirpath_prefix root lg))
    in
    if success then
      (* Only keep partial path in the same "-R" block *)
      full, add_path path_root (ph, lg) others
    else
      full, others in
  let full, others = aux !load_paths in
  (* Returns the dirpath matching exactly and the ordered list of
     -R/-Q blocks with subdirectories that matches *)
  full, List.map snd others

let locate_file fname =
  let paths = List.map physical !load_paths in
  let _,longfname =
    System.find_file_in_path ~warn:(not !Flags.quiet) paths fname in
  longfname

(************************************************************************)
(*s Locate absolute or partially qualified library names in the path *)

module Error = struct
  type t = LibUnmappedDir | LibNotFound

  let unmapped_dir qid =
    let prefix, _ = Libnames.repr_qualid qid in
    CErrors.user_err
      Pp.(seq [ str "Cannot load "; Libnames.pr_qualid qid; str ":"; spc ()
              ; str "no physical path bound to"; spc ()
              ; Names.DirPath.print prefix; fnl ()
              ])

  let lib_not_found dir =
    let vos = !Flags.load_vos_libraries in
    let vos_msg = if vos then [Pp.str " (while searching for a .vos file)"] else [] in
    CErrors.user_err
      Pp.(seq ([ str "Cannot find library "; Names.DirPath.print dir; str" in loadpath"]@vos_msg))

  let raise dp = function
    | LibUnmappedDir ->
      unmapped_dir (Libnames.qualid_of_dirpath dp)
    | LibNotFound ->
      lib_not_found dp
end

(* If [!Flags.load_vos_libraries]
      and the .vos file exists
      and this file is not empty
   Then load this library
   Else load the .vo file or raise error if both are missing *)
let select_vo_file ~find base =
  let find ext =
    try
      let name = Names.Id.to_string base ^ ext in
      let lpath, file = find name in
      Ok (lpath, file)
    with Not_found -> Error Error.LibNotFound in
  if !Flags.load_vos_libraries
  then begin
    match find ".vos" with
    | Ok (_, vos as resvos) when (Unix.stat vos).Unix.st_size > 0 -> Ok resvos
    | _ -> find ".vo"
  end
  else find ".vo"

let find_first loadpath base =
  match System.all_in_path loadpath base with
  | [] -> raise Not_found
  | f :: _ -> f

let find_unique fullqid loadpath base =
  match System.all_in_path loadpath base with
  | [] -> raise Not_found
  | [f] -> f
  | _::_ as l ->
    CErrors.user_err Pp.(str "Required library " ++ Libnames.pr_qualid fullqid ++
      strbrk " matches several files in path (found " ++ pr_enum str (List.map snd l) ++ str ").")

let locate_absolute_library dir : (CUnix.physical_path, Error.t) Result.t =
  (* Search in loadpath *)
  let pref, base = Libnames.split_dirpath dir in
  let loadpath = filter_path (fun dir -> DP.equal dir pref) in
  match loadpath with
  | [] -> Error LibUnmappedDir
  | _ ->
    match select_vo_file ~find:(find_first loadpath) base with
    | Ok (_, file) -> Ok file
    | Error fail -> Error fail

let locate_qualified_library ?root qid :
  (DP.t * CUnix.physical_path, Error.t) Result.t =
  (* Search library in loadpath *)
  let dir, base = Libnames.repr_qualid qid in
  match expand_path ?root dir with
  | [], [] -> Error LibUnmappedDir
  | full_matches, others ->
    let result =
      (* Priority to exact matches *)
      match select_vo_file ~find:(find_first full_matches) base with
      | Ok _ as x -> x
      | Error _ ->
         (* Looking otherwise in -R/-Q blocks of partial matches *)
        let rec aux = function
          | [] -> Error Error.LibUnmappedDir
          | block :: rest ->
            match select_vo_file ~find:(find_unique qid block) base with
            | Ok _ as x -> x
            | Error _ -> aux rest
        in
        aux others
    in
    match result with
    | Ok (dir,file) ->
      let library = Libnames.add_dirpath_suffix dir base in
      Ok (library, file)
    | Error _ as e -> e

let warn_deprecated_missing_stdlib =
  CWarnings.create ~name:"deprecated-missing-stdlib"
    ~category:Deprecation.Version.v9_0
    (fun qid ->
      Pp.(str "Loading Stdlib without prefix is deprecated." ++ spc ()
          ++ str "Use \"From Stdlib Require " ++ Libnames.pr_qualid qid
          ++ str "\"" ++ spc() ++ str "or the deprecated \"From Coq Require "
          ++ Libnames.pr_qualid qid ++ str "\"" ++ spc ()
          ++ str "for compatibility with older Coq versions."))

(* temporary handling deprecated loading of stdlib without root *)
let locate_qualified_library ?root qid =
  let root_stdlib =
    Names.(Libnames.add_dirpath_suffix DirPath.empty (Id.of_string "Stdlib")) in
  match root, locate_qualified_library ?root qid with
  | Some _, r | None, (Ok _ as r) -> r
  | None, (Error _ as e) ->
     match locate_qualified_library ~root:root_stdlib qid with
     | Error _ -> e
     | Ok _ as o -> warn_deprecated_missing_stdlib ?loc:qid.loc qid; o

(** { 5 Extending the load path } *)

type vo_path =
  { unix_path : string
  (** Filesystem path containing vo/ml files *)
  ; coq_path  : DP.t
  (** Coq prefix for the path *)
  ; implicit  : bool
  (** [implicit = true] avoids having to qualify with [coq_path]
      true for -R, false for -Q in command line *)
  ; recursive : bool
  (** [recursive] will determine whether we explore sub-directories  *)
  }

let warn_cannot_open_path =
  CWarnings.create ~name:"cannot-open-path" ~category:CWarnings.CoreCategories.filesystem
    (fun unix_path -> Pp.(str "Cannot open " ++ str unix_path))

let warn_cannot_use_directory =
  CWarnings.create ~name:"cannot-use-directory" ~category:CWarnings.CoreCategories.filesystem
    (fun d ->
       Pp.(str "Directory " ++ str d ++
           strbrk " cannot be used as a Rocq identifier (skipped)"))

let convert_string d =
  try Names.Id.of_string d
  with
  | CErrors.UserError _ ->
    let d = Unicode.escaped_if_non_utf8 d in
    warn_cannot_use_directory d;
    raise_notrace Exit

let add_vo_path lp =
  let unix_path = lp.unix_path in
  let implicit = lp.implicit in
  let recursive = lp.recursive in
  if System.exists_dir unix_path then
    let dirs = if recursive then System.all_subdirs ~unix_path else [] in
    let dirs = List.sort (fun a b -> String.compare (fst a) (fst b)) dirs in
    let prefix = DP.repr lp.coq_path in
    let convert_dirs (lp, cp) =
      try
        let path = List.rev_map convert_string cp @ prefix in
        Some (lp, DP.make path)
      with Exit -> None
    in
    let dirs = List.map_filter convert_dirs dirs in
    let root = (unix_path,lp.coq_path) in
    let add (path, dir) = add_load_path root path ~implicit dir in
    (* deeper dirs registered first and thus be found last *)
    let dirs = List.rev dirs in
    let () = List.iter add dirs in
    add_load_path root unix_path ~implicit lp.coq_path
  else
    warn_cannot_open_path unix_path
