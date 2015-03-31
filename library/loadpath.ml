(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Errors
open Names
open Libnames

(** Load paths. Mapping from physical to logical paths. *)

type t = {
  path_physical : CUnix.physical_path;
  path_logical : DirPath.t;
  path_implicit : bool;
}

let load_paths = Summary.ref ([] : t list) ~name:"LOADPATHS"

let logical p = p.path_logical

let physical p = p.path_physical

let get_load_paths () = !load_paths

let get_paths () = List.map physical !load_paths

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
    if DirPath.equal p.path_logical dir then p.path_physical :: aux l
    else aux l
  in
  aux !load_paths

let is_suffix dir1 dir2 =
  let dir1 = DirPath.repr dir1 in
  let dir2 = DirPath.repr dir2 in
  List.prefix_of Id.equal dir1 dir2

let expand_path dir =
  let rec aux = function
  | [] -> []
  | p :: l ->
    let { path_physical = ph; path_logical = lg } = p in
    match p.path_implicit with
    | true ->
      (** The path is implicit, so that we only want match the logical suffix *)
      if is_suffix dir lg then (ph, lg) :: aux l else aux l
    | false ->
      (** Otherwise we must match exactly *)
      if DirPath.equal dir lg then (ph, lg) :: aux l else aux l
  in
  aux !load_paths
