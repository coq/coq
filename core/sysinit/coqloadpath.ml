(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Pp

(* Recursively puts `.v` files in the LoadPath *)
let build_stdlib_vo_path ~unix_path ~coq_path =
  let open Loadpath in
  { unix_path; coq_path ; has_ml = false; implicit = true; recursive = true }

(* Note we don't use has_ml=true due to #12771 , we need to see if we
   should just remove that option *)
let build_userlib_path ~unix_path =
  let open Loadpath in
  if Sys.file_exists unix_path then
    let ml_path = System.all_subdirs ~unix_path |> List.map fst in
    let vo_path =
      { unix_path
      ; coq_path = Libnames.default_root_prefix
      ; has_ml = false
      ; implicit = false
      ; recursive = true
      } in
    ml_path, [vo_path]
  else [], []

(* LoadPath for Coq user libraries *)
let init_load_path ~coqenv =

  let open Loadpath in
  let user_contrib = Boot.Env.user_contrib coqenv |> Boot.Path.to_string in
  let xdg_dirs = Envars.xdg_dirs ~warn:(fun x -> Feedback.msg_warning (str x)) in
  let coqpath = Envars.coqpath in
  let coq_path = Names.DirPath.make [Libnames.coq_root] in

  (* ML includes *)
  let unix_path = Boot.Env.plugins coqenv |> Boot.Path.to_string in
  let plugins_dirs = System.all_subdirs ~unix_path |> List.map fst in
  let stdlib = Boot.Env.stdlib coqenv |> Boot.Path.to_string in
  let contrib_ml, contrib_vo = build_userlib_path ~unix_path:user_contrib in

  let misc_ml, misc_vo =
    List.map (fun s -> build_userlib_path ~unix_path:s) (xdg_dirs @ coqpath) |> List.split in

  let ml_loadpath = plugins_dirs @ contrib_ml @ List.concat misc_ml in
  let vo_loadpath =
    (* current directory (not recursively!) *)
    [ { unix_path = "."
      ; coq_path = Libnames.default_root_prefix
      ; implicit = false
      ; has_ml = true
      ; recursive = false
      } ] @

    (* then standard library *)
    [build_stdlib_vo_path ~unix_path:stdlib ~coq_path] @

    (* then user-contrib *)
    contrib_vo @

    (* then directories in XDG_DATA_DIRS and XDG_DATA_HOME and COQPATH *)
    List.concat misc_vo
  in
  ml_loadpath, vo_loadpath
