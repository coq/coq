(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Error = struct

  type t =
    | CannotFindMeta of string * string
    | CannotParseMetaFile of string * string
    | DeclaredMLModuleNotFound of string * string * string
    | MetaLacksFieldForPackage of string * string * string

  type _ CErrors.tag += FlError : t CErrors.tag

  open struct let raise e = CErrors.coq_error FlError e end

  let no_meta f package = raise @@ CannotFindMeta (f, package)
  let cannot_parse_meta_file file msg = raise @@ CannotParseMetaFile (file,msg)
  let declare_in_META f s m = raise @@ DeclaredMLModuleNotFound (f, s, m)
  let meta_file_lacks_field meta_file package field = raise @@ MetaLacksFieldForPackage (meta_file, package, field)

  let () = CErrors.register (module struct
      type e = t
      type _ CErrors.tag += T = FlError

      let pp = let open Pp in function
        | CannotFindMeta (f, package) ->
          str "in file" ++ spc () ++ str f ++ str "," ++ spc ()
          ++ str "could not find META." ++ str package ++ str "."
        | CannotParseMetaFile (file, msg) ->
          str "META file \"" ++ str file ++ str "\":" ++ spc ()
          ++ str "Syntax error:" ++ spc () ++ str msg
        | DeclaredMLModuleNotFound (f, s, m) ->
          str "in file " ++ str f ++ str "," ++ spc() ++ str "declared ML module" ++ spc ()
          ++ str s ++ spc () ++ str "has not been found in" ++ spc () ++ str m ++ str "."
        | MetaLacksFieldForPackage (meta_file, package, field) ->
          str "META file \"" ++ str meta_file ++ str "\"" ++ spc () ++ str "lacks field" ++ spc ()
          ++ str field ++ spc () ++ str "for package" ++ spc () ++ str package ++ str "."
    end)
end

(* Platform build is doing something weird with META, hence we parse
   when finding, but at some point we should find, then parse. *)
let parse_META meta_file package =
  try
    let ic = open_in meta_file in
    let m = Fl_metascanner.parse ic in
    close_in ic;
    Some m
  with
  (* This should not be necessary, but there's a problem in the platform build *)
  | Sys_error _msg -> None
  (* findlib >= 1.9.3 uses its own Error exception, so we can't catch
     it without bumping our version requirements. TODO pass the message on once we bump. *)
  | _ -> Error.cannot_parse_meta_file package ""

let rec find_parsable_META meta_files package =
  match meta_files with
  | [] ->
    (try
       let meta_file = Findlib.package_meta_file package in
       Option.map (fun meta -> meta_file, meta) (parse_META meta_file package)
     with Fl_package_base.No_such_package _ -> None)
  | meta_file :: ms ->
    if String.equal (Filename.extension meta_file) ("." ^ package)
    then Option.map (fun meta -> meta_file, meta) (parse_META meta_file package)
    else find_parsable_META ms package

let rec find_plugin_field_opt fld = function
  | [] ->
    None
  | { Fl_metascanner.def_var; def_value; _ } :: rest ->
    if String.equal def_var fld
    then Some def_value
    else find_plugin_field_opt fld rest

let find_plugin_field fld def pkgs =
  Option.default def (find_plugin_field_opt fld pkgs)

let rec find_plugin meta_file plugin_name path p { Fl_metascanner.pkg_defs ; pkg_children  } =
  match p with
  | [] -> path, pkg_defs
  | p :: ps ->
    let c =
      match CList.assoc_f_opt String.equal p pkg_children with
      | None -> Error.declare_in_META meta_file (String.concat "." plugin_name) meta_file
      | Some c -> c
    in
    let path = path @ [find_plugin_field "directory" "." c.Fl_metascanner.pkg_defs] in
    find_plugin meta_file plugin_name path ps c

let findlib_resolve ~meta_files ~file ~package ~plugin_name =
  match find_parsable_META meta_files package with
  | None -> Error.no_meta file package
  | Some (meta_file, meta) ->
    (* let meta = parse_META meta_file package in *)
    let path = [find_plugin_field "directory" "." meta.Fl_metascanner.pkg_defs] in
    let path, plug = find_plugin meta_file plugin_name path plugin_name meta in
    let cmxs_file =
      match find_plugin_field_opt "plugin" plug with
      | None ->
        Error.meta_file_lacks_field meta_file package "plugin"
      | Some res_file ->
        String.concat "/" path ^ "/" ^ Filename.chop_extension res_file
    in
    meta_file, cmxs_file
