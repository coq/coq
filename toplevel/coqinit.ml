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

let ( / ) s1 s2 = Filename.concat s1 s2

let set_debug () =
  let () = Exninfo.record_backtrace true in
  Flags.debug := true

(* Loading of the resource file.
   rcfile is either $XDG_CONFIG_HOME/.coqrc.VERSION, or $XDG_CONFIG_HOME/.coqrc if the first one
  does not exist. *)

let rcdefaultname = "coqrc"

let load_rcfile ~rcfile ~state =
    try
      match rcfile with
      | Some rcfile ->
        if CUnix.file_readable_p rcfile then
          Vernac.load_vernac ~echo:false ~interactive:false ~check:true ~state rcfile
        else raise (Sys_error ("Cannot read rcfile: "^ rcfile))
      | None ->
        try
          let warn x = Feedback.msg_warning (str x) in
          let inferedrc = List.find CUnix.file_readable_p [
            Envars.xdg_config_home warn / rcdefaultname^"."^Coq_config.version;
            Envars.xdg_config_home warn / rcdefaultname;
            Envars.home ~warn / "."^rcdefaultname^"."^Coq_config.version;
            Envars.home ~warn / "."^rcdefaultname
          ] in
          Vernac.load_vernac ~echo:false ~interactive:false ~check:true ~state inferedrc
        with Not_found -> state
        (*
        Flags.if_verbose
          mSGNL (str ("No coqrc or coqrc."^Coq_config.version^
                         " found. Skipping rcfile loading."))
        *)
    with reraise ->
      let reraise = Exninfo.capture reraise in
      let () = Feedback.msg_info (str"Load of rcfile failed.") in
      Exninfo.iraise reraise

(* Recursively puts `.v` files in the LoadPath *)
let build_stdlib_vo_path ~unix_path ~coq_path =
  let open Loadpath in
  { unix_path; coq_path ; has_ml = false; implicit = true; recursive = true }

let build_userlib_path ~unix_path =
  let open Loadpath in
  { unix_path
  ; coq_path = Libnames.default_root_prefix
  ; has_ml = true
  ; implicit = false
  ; recursive = true
  }

(* LoadPath for Coq user libraries *)
let libs_init_load_path ~coqlib =

  let open Loadpath in
  let user_contrib = coqlib/"user-contrib" in
  let xdg_dirs = Envars.xdg_dirs ~warn:(fun x -> Feedback.msg_warning (str x)) in
  let coqpath = Envars.coqpath in
  let coq_path = Names.DirPath.make [Libnames.coq_root] in

  (* ML includes *)
  let plugins_dirs = System.all_subdirs ~unix_path:(coqlib/"plugins") in
  List.map fst plugins_dirs,

  (* current directory (not recursively!) *)
  [ { unix_path = "."
    ; coq_path = Libnames.default_root_prefix
    ; implicit = false
    ; has_ml = true
    ; recursive = false
    } ] @

  (* then standard library *)
  [build_stdlib_vo_path ~unix_path:(coqlib/"theories") ~coq_path] @

  (* then user-contrib *)
  (if Sys.file_exists user_contrib then
     [build_userlib_path ~unix_path:user_contrib] else []
  ) @

  (* then directories in XDG_DATA_DIRS and XDG_DATA_HOME and COQPATH *)
  List.map (fun s -> build_userlib_path ~unix_path:s) (xdg_dirs @ coqpath)
