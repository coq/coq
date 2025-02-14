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
open Pp

(* Recursively puts `.v` files in the LoadPath *)
let build_stdlib_vo_path ~unix_path ~rocq_path =
  let open Loadpath in
  { unix_path; coq_path = rocq_path; implicit = true; recursive = true }

let build_userlib_path ~unix_path =
  let open Loadpath in
  if Sys.file_exists unix_path then
    let vo_path =
      { unix_path
      ; coq_path = Libnames.default_root_prefix
      ; implicit = false
      ; recursive = true
      } in
    [vo_path]
  else []

(* LoadPath for Rocq user libraries *)
let init_load_path ~coqenv =

  let open Loadpath in
  let user_contrib = Boot.Env.user_contrib coqenv |> Boot.Path.to_string in
  let xdg_dirs = Envars.xdg_dirs ~warn:(fun x -> Feedback.msg_warning (str x)) in
  let rocqpath = Envars.coqpath in
  let rocq_path = Names.DirPath.make [Libnames.rocq_init_root] in
  (* ML includes *)
  let core_dir = Boot.Env.corelib coqenv in

  (* EJGA: this needs clenaup, we must be deterministic *)
  let meta_dir = if Boot.Env.Path.(exists (relative core_dir "META"))
    then [Boot.Env.Path.(to_string (relative core_dir ".."))]
    else []
  in
  let stdlib = Boot.Env.stdlib coqenv |> Boot.Path.to_string in
  let contrib_vo = build_userlib_path ~unix_path:user_contrib in

  let misc_vo =
    List.map (fun s -> build_userlib_path ~unix_path:s) (xdg_dirs @ (rocqpath())) in

  let ml_loadpath = meta_dir in
  let vo_loadpath =
    (* current directory (not recursively!) *)
    [ { unix_path = "."
      ; coq_path = Libnames.default_root_prefix
      ; implicit = false
      ; recursive = false
      } ] @

    (* then standard library *)
    [build_stdlib_vo_path ~unix_path:stdlib ~rocq_path] @

    (* then user-contrib *)
    contrib_vo @

    (* then directories in XDG_DATA_DIRS and XDG_DATA_HOME and ROCQPATH *)
    List.concat misc_vo
  in
  ml_loadpath, vo_loadpath
