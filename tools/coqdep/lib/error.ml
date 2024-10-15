(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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

let () = CErrors.register_handler @@ function
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
    Some Pp.(str "in file " ++ quote (str f) ++ str "." ++ spc () ++ str "The name "
      ++ quote (str s) ++ strbrk " is no longer a valid plugin name." ++ spc ()
      ++ strbrk "Plugins should be loaded using their public name according to \
      findlib, for example " ++ quote (str "package-name.foo") ++ str " and not "
      ++ quote (str "foo_plugin") ++ str "." ++ spc () ++ strbrk "If you are \
      using a build system that does not yet support the new loading method \
      (such as Dune) you must specify both the legacy and the findlib plugin \
      name as in:" ++ spc ()
      ++ str "      Declare ML Module \"foo_plugin:package-name.foo\".")

  | _ -> None

let cannot_parse s ij = raise @@ CannotParseFile (s, ij)
let cannot_open_project_file msg = raise @@ CannotOpenProjectFile msg
let cannot_parse_project_file file msg = raise @@ CannotParseProjectFile (file, msg)
let cannot_open s msg = raise @@ CannotOpenFile (s, msg)
let findlib_name f s = raise @@ InvalidFindlibPluginName (f, s)
