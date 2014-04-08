(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Errors
open Names
open Libnames

type path_type = ImplicitPath | ImplicitRootPath | RootPath

(** Load paths. Mapping from physical to logical paths. *)

type t = {
  path_physical : CUnix.physical_path;
  path_logical : DirPath.t;
  path_type : path_type;
}

let load_paths = Summary.ref ([] : t list) ~name:"LOADPATHS"

let accessible_paths =
  Summary.ref ([] : CUnix.physical_path list) ~name:"ACCPATHS"

let logical p = p.path_logical

let physical p = p.path_physical

let get_load_paths () = !load_paths

let get_paths () = List.map physical !load_paths

let get_accessible_paths () = !accessible_paths

let anomaly_too_many_paths path =
  anomaly (str "Several logical paths are associated to" ++ spc () ++ str path)

let find_load_path phys_dir =
  let phys_dir = CUnix.canonical_path_name phys_dir in
  let filter p = String.equal p.path_physical phys_dir in
  let paths = List.filter filter !load_paths in
  match paths with
  | [] -> raise Not_found
  | [p] -> p
  | _ -> anomaly_too_many_paths phys_dir

let is_in_load_paths phys_dir =
  let dir = CUnix.canonical_path_name phys_dir in
  let lp = get_load_paths () in
  let check_p p = String.equal dir p.path_physical in
  List.exists check_p lp

let remove_load_path dir =
  let filter p = not (String.equal p.path_physical dir) in
  load_paths := List.filter filter !load_paths

let add_load_path phys_path path_type coq_path =
  let phys_path = CUnix.canonical_path_name phys_path in
  let filter p = String.equal p.path_physical phys_path in
  let binding = {
    path_logical = coq_path;
    path_physical = phys_path;
    path_type = path_type;
  } in
  match List.filter filter !load_paths with
  | [] ->
    load_paths := binding :: !load_paths;
    if path_type <> ImplicitPath then
      accessible_paths := List.fold_left (fun acc v -> (fst v) :: acc)
	(phys_path :: !accessible_paths) (System.all_subdirs phys_path)
  | [p] ->
    let dir = p.path_logical in
    if not (DirPath.equal coq_path dir)
      (* If this is not the default -I . to coqtop *)
      && not
      (String.equal phys_path (CUnix.canonical_path_name Filename.current_dir_name)
          && DirPath.equal coq_path (Nameops.default_root_prefix))
    then
      begin
        (* Assume the user is concerned by library naming *)
        if not (DirPath.equal dir Nameops.default_root_prefix) then
          msg_warning
            (str phys_path ++ strbrk " was previously bound to " ++
              pr_dirpath dir ++ strbrk "; it is remapped to " ++
              pr_dirpath coq_path);
        remove_load_path phys_path;
        load_paths := binding :: !load_paths;
      end
  | _ -> anomaly_too_many_paths phys_path

let extend_path_with_dirpath p dir =
  List.fold_left Filename.concat p
    (List.rev_map Id.to_string (DirPath.repr dir))

let expand_root_path dir =
  let rec aux = function
  | [] -> []
  | p :: l ->
    if p.path_type <> ImplicitPath && is_dirpath_prefix_of p.path_logical dir then
      let suffix = drop_dirpath_prefix p.path_logical dir in
      extend_path_with_dirpath p.path_physical suffix :: aux l
    else aux l
  in
  aux !load_paths

(* Root p is bound to A.B.C.D and we require file C.D.E.F *)
(* We may mean A.B.C.D.E.F, or A.B.C.D.C.D.E.F *)

(* Root p is bound to A.B.C.C and we require file C.C.E.F *)
(* We may mean A.B.C.C.E.F, or A.B.C.C.C.E.F, or A.B.C.C.C.C.E.F *)

let intersections d1 d2 =
  let rec aux d1 =
    if DirPath.is_empty d1 then [d2] else
      let rest = aux (snd (chop_dirpath 1 d1)) in
      if is_dirpath_prefix_of d1 d2 then drop_dirpath_prefix d1 d2 :: rest
      else rest in
  aux d1

let expand p dir =
  let ph = extend_path_with_dirpath p.path_physical dir in
  let log = append_dirpath p.path_logical dir in
  (ph, log)

let expand_path dir =
  let rec aux = function
  | [] -> []
  | p :: l ->
    match p.path_type with
    | ImplicitPath -> expand p dir :: aux l
    | ImplicitRootPath ->
      let inters = intersections p.path_logical dir in
      List.map (expand p) inters @ aux l
    | RootPath ->
      if is_dirpath_prefix_of p.path_logical dir then
	expand p (drop_dirpath_prefix p.path_logical dir) :: aux l
      else aux l in
  aux !load_paths
