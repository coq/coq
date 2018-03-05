(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Util
open CErrors
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

let anomaly_too_many_paths path =
  anomaly (str "Several logical paths are associated to" ++ spc () ++ str path ++ str ".")

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

let warn_overriding_logical_loadpath =
  CWarnings.create ~name:"overriding-logical-loadpath" ~category:"loadpath"
         (fun (phys_path, old_path, coq_path) ->
          str phys_path ++ strbrk " was previously bound to " ++
            DirPath.print old_path ++ strbrk "; it is remapped to " ++
            DirPath.print coq_path)

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
      if DirPath.equal coq_path old_path then
        implicit <> old_implicit
      else
        let () =
          (* Do not warn when overriding the default "-I ." path *)
          if not (DirPath.equal old_path Libnames.default_root_prefix) then
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
        if implicit then is_dirpath_suffix_of dir lg
        else DirPath.equal dir lg
      | Some root ->
        is_dirpath_prefix_of root lg &&
          is_dirpath_suffix_of dir (drop_dirpath_prefix root lg) in
    if success then (ph, lg) :: aux l else aux l in
  aux !load_paths

let locate_file fname =
  let paths = List.map physical !load_paths in
  let _,longfname =
    System.find_file_in_path ~warn:(not !Flags.quiet) paths fname in
  longfname
