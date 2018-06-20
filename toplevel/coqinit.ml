(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Pp

let ( / ) s1 s2 = s1 ^ "/" ^ s2

let set_debug () =
  let () = Backtrace.record_backtrace true in
  Flags.debug := true

(* Loading of the ressource file.
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
      let reraise = CErrors.push reraise in
      let () = Feedback.msg_info (str"Load of rcfile failed.") in
      iraise reraise

(* Recursively puts dir in the LoadPath if -nois was not passed *)
let build_stdlib_path ~load_init ~unix_path ~coq_path ~with_ml =
  let open Mltop in
  let add_ml = if with_ml then AddRecML else AddNoML in
  { recursive = true;
    path_spec = VoPath { unix_path; coq_path ; has_ml = add_ml; implicit = load_init }
  }

let build_userlib_path ~unix_path =
  let open Mltop in
  { recursive = true;
    path_spec = VoPath {
        unix_path;
        coq_path = Libnames.default_root_prefix;
        has_ml = Mltop.AddRecML;
        implicit = false;
      }
  }

let ml_path_if c p =
  let open Mltop in
  let f x = { recursive = false; path_spec = MlPath x } in
  if c then List.map f p else []

(* LoadPath for developers *)
let toplevel_init_load_path () =
  let coqlib = Envars.coqlib () in
  (* NOTE: These directories are searched from last to first *)
  (* first, developer specific directory to open *)
  ml_path_if Coq_config.local [coqlib/"dev"]

(* LoadPath for Coq user libraries *)
let libs_init_load_path ~load_init =

  let open Mltop in
  let coqlib = Envars.coqlib () in
  let user_contrib = coqlib/"user-contrib" in
  let xdg_dirs = Envars.xdg_dirs ~warn:(fun x -> Feedback.msg_warning (str x)) in
  let coqpath = Envars.coqpath in
  let coq_path = Names.DirPath.make [Libnames.coq_root] in

  (* current directory (not recursively!) *)
  [ { recursive = false;
      path_spec = VoPath { unix_path = ".";
                           coq_path = Libnames.default_root_prefix;
                           implicit = false;
                           has_ml = AddTopML }
    } ] @

  (* then standard library and plugins *)
  [build_stdlib_path ~load_init ~unix_path:(coqlib/"theories") ~coq_path ~with_ml:false;
   build_stdlib_path ~load_init ~unix_path:(coqlib/"plugins")  ~coq_path ~with_ml:true ] @

  (* then user-contrib *)
  (if Sys.file_exists user_contrib then
     [build_userlib_path ~unix_path:user_contrib] else []
  ) @

  (* then directories in XDG_DATA_DIRS and XDG_DATA_HOME and COQPATH *)
  List.map (fun s -> build_userlib_path ~unix_path:s) (xdg_dirs @ coqpath)

(* Initialises the Ocaml toplevel before launching it, so that it can
   find the "include" file in the *source* directory *)
let init_ocaml_path () =
  let open Mltop in
  let lp s = { recursive = false; path_spec = MlPath s } in
  let add_subdir dl =
    Mltop.add_coq_path (lp (List.fold_left (/) Envars.coqroot [dl]))
  in
    Mltop.add_coq_path (lp (Envars.coqlib ()));
    List.iter add_subdir Coq_config.all_src_dirs
