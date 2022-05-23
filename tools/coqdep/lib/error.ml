(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

exception CannotParseFile of string * (int * int)
exception CannotParseProjectFile of string * string
exception CannotParseMetaFile of string * string

exception CannotOpenFile of string * string
exception CannotOpenProjectFile of string

exception MetaLacksFieldForPackage of string * string * string
exception DeclaredMLModuleNotFound of string * string * string
exception InvalidFindlibPluginName of string * string
exception CannotFindMeta of string * string

let _ = CErrors.register_handler @@ function
  | CannotParseFile (s,(i,j)) ->
    Some Pp.(str "File \"" ++ str s ++ str "\"," ++ str "characters" ++ spc ()
      ++ int i ++ str "-" ++ int j ++ str ":" ++ spc () ++ str "Syntax error")

  | CannotParseProjectFile (file, msg) ->
    Some Pp.(str "Project file" ++ spc () ++ str  "\"" ++ str file ++ str "\":" ++ spc ()
      ++ str "Syntax error:" ++ str msg)

  | CannotParseMetaFile (file, msg) ->
    Some Pp.(str "META file \"" ++ str file ++ str "\":" ++ spc ()
      ++ str "Syntax error:" ++ spc () ++ str msg)

  | CannotOpenFile (s, msg) ->
    Some Pp.(str s ++ str ":" ++ spc () ++ str msg)

  | CannotOpenProjectFile msg ->
    (* TODO: more info? *)
    Some Pp.(str msg)

  | MetaLacksFieldForPackage (meta_file, package, field) ->
    Some Pp.(str "META file \"" ++ str meta_file ++ str "\"" ++ spc () ++ str "lacks field" ++ spc ()
      ++ str field ++ spc () ++ str "for package" ++ spc () ++ str package ++ str ".")

  | DeclaredMLModuleNotFound (f, s, m) ->
    Some Pp.(str "in file " ++ str f ++ str "," ++ spc() ++ str "declared ML module" ++ spc ()
      ++ str s ++ spc () ++ str "has not been found in" ++ spc () ++ str m ++ str ".")

  | InvalidFindlibPluginName (f, s) ->
    Some Pp.(str (Printf.sprintf "in file %s, %s is not a valid plugin name anymore." f s)
      ++ str "Plugins should be loaded using their public name according to findlib," ++ spc ()
      ++ str "for example package-name.foo and not foo_plugin." ++ spc ()
      ++ str "If you are building with dune < 2.9.4 you must specify both" ++ spc ()
      ++ str "the legacy and the findlib plugin name as in:" ++ spc ()
      ++ str "Declare ML Module \"foo_plugin:package-name.foo\".")

  | CannotFindMeta (f, package) ->
    Some Pp.(str "in file" ++ spc () ++ str f ++ str "," ++ spc ()
      ++ str "could not find META." ++ str package ++ str ".")

  | _ -> None

let cannot_parse s ij = raise @@ CannotParseFile (s, ij)
let cannot_open_project_file msg = raise @@ CannotOpenProjectFile msg
let cannot_parse_project_file file msg = raise @@ CannotParseProjectFile (file, msg)
let cannot_parse_meta_file file msg = raise @@ CannotParseMetaFile (file, msg)
let meta_file_lacks_field meta_file package field = raise @@ MetaLacksFieldForPackage (meta_file, package, field)
let cannot_open s msg = raise @@ CannotOpenFile (s, msg)
let declare_in_META f s m = raise @@ DeclaredMLModuleNotFound (f, s, m)
let findlib_name f s = raise @@ InvalidFindlibPluginName (f, s)
let no_meta f package = raise @@ CannotFindMeta (f, package)
