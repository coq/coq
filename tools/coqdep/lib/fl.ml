(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open File_util

let coqc_predicates = ["native"]

module Fl_internals = struct
  (** Functions not exported by findlib (XXX there is a copy in mltop, we should share them) *)

  (* Fl_split.in_words is not exported *)
  let fl_split_in_words s =
    (* splits s in words separated by commas and/or whitespace *)
    let l = String.length s in
    let rec split i j =
      if j < l then
        match s.[j] with
        | (' '|'\t'|'\n'|'\r'|',') ->
          if i<j then (String.sub s i (j-i)) :: (split (j+1) (j+1))
          else split (j+1) (j+1)
        |	_ ->
          split i (j+1)
      else
      if i<j then [ String.sub s i (j-i) ] else []
    in
    split 0 0

  (* simulate what fl_dynload does *)
  let fl_find_plugins lib =
    let base = Findlib.package_directory lib in
    let archive = try Findlib.package_property coqc_predicates lib "plugin"
      with Not_found ->
      try fst (Findlib.package_property_2 ("plugin"::coqc_predicates) lib "archive")
      with Not_found -> ""
    in
    fl_split_in_words archive |> List.map (Findlib.resolve_path ~base)

  (* first string is the v file which triggered the error, rest is Fl_package_base.No_such_package *)
  exception No_such_package of string * string * string

  let () = CErrors.register_handler Pp.(function
      | No_such_package(vfile,p,msg) ->
        let paths = Findlib.search_path () in
        Some (hov 0 (str "In file" ++ spc() ++ str vfile ++ spc() ++
                     str "findlib error: " ++ str p ++ str " not found in:" ++ cut () ++
                     v 0 (prlist_with_sep cut str paths) ++ fnl() ++ str msg))
      | _ ->
        None
    )

end

let relative_if_dune path =
  (* relativize the path if inside the current dune workspace
     if we relativize paths outside the dune workspace it fails so make sure to avoid it *)
  match Sys.getenv_opt "DUNE_SOURCEROOT" with
  | Some dune when CString.is_prefix dune path ->
    normalize_path (to_relative_path path)
  | _ -> normalize_path path

let findlib_resolve ~package =
  let meta_file = Findlib.package_meta_file package in
  let cmxss = Fl_internals.fl_find_plugins package in
  let meta_file = relative_if_dune meta_file in
  let cmxs_file = List.map relative_if_dune cmxss in
  (meta_file, cmxs_file)

let static_libs = CString.Set.of_list Static_toplevel_libs.static_toplevel_libs

let findlib_deep_resolve ~package =
  let packages = Findlib.package_deep_ancestors coqc_predicates [package] in
  let packages = CList.filter (fun package ->
      not (CString.Set.mem package static_libs))
      packages
  in
  List.fold_left (fun (metas,cmxss) package ->
      let meta, cmxss' = findlib_resolve ~package in
      meta :: metas, cmxss' @ cmxss)
    ([],[])
    packages

let findlib_deep_resolve ~file ~package =
  try findlib_deep_resolve ~package
  with Fl_package_base.No_such_package(p,m) ->
    raise (Fl_internals.No_such_package (file,p,m))

module Internal = struct
  let get_worker_path () =
    let top = "rocqworker" in
    let dir = Findlib.package_directory "rocq-runtime" in
    let exe = if Sys.(os_type = "Win32" || os_type = "Cygwin") then ".exe" else "" in
    let file = Filename.concat dir (top^exe) in
    match Sys.getenv_opt "DUNE_SOURCEROOT" with
    | Some dune when CString.is_prefix dune file ->
      normalize_path (to_relative_path file)
    | _ -> normalize_path file
end
