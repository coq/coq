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

exception CannotOpenFile of string * string
exception CannotOpenProjectFile of string

exception InvalidFindlibPluginName of string * string

let _ = CErrors.register_handler @@ function
  | CannotParseFile (s,(i,j)) ->
    Some Pp.(str "File \"" ++ str s ++ str "\"," ++ str "characters" ++ spc ()
      ++ int i ++ str "-" ++ int j ++ str ":" ++ spc () ++ str "Syntax error")

  | CannotParseProjectFile (file, msg) ->
    Some Pp.(str "Project file" ++ spc () ++ str  "\"" ++ str file ++ str "\":" ++ spc ()
      ++ str "Syntax error:" ++ str msg)

  | CannotOpenFile (s, msg) ->
    Some Pp.(str s ++ str ":" ++ spc () ++ str msg)

  | CannotOpenProjectFile msg ->
    (* TODO: more info? *)
    Some Pp.(str msg)

  | InvalidFindlibPluginName (f, s) ->
    Some Pp.(str (Printf.sprintf "in file %s, %s is not a valid plugin name anymore." f s)
      ++ str "Plugins should be loaded using their public name according to findlib," ++ spc ()
      ++ str "for example package-name.foo and not foo_plugin." ++ spc ()
      ++ str "If you are building with dune < 2.9.4 you must specify both" ++ spc ()
      ++ str "the legacy and the findlib plugin name as in:" ++ spc ()
      ++ str "Declare ML Module \"foo_plugin:package-name.foo\".")

  | _ -> None

let cannot_parse s ij = raise @@ CannotParseFile (s, ij)
let cannot_open_project_file msg = raise @@ CannotOpenProjectFile msg
let cannot_parse_project_file file msg = raise @@ CannotParseProjectFile (file, msg)
let cannot_open s msg = raise @@ CannotOpenFile (s, msg)
let findlib_name f s = raise @@ InvalidFindlibPluginName (f, s)
