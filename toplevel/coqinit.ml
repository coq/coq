(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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
let rcfile = ref ""
let rcfile_specified = ref false
let set_rcfile s = rcfile := s; rcfile_specified := true

let load_rc = ref true
let no_load_rc () = load_rc := false

let load_rcfile ~time doc sid =
  if !load_rc then
    try
      if !rcfile_specified then
        if CUnix.file_readable_p !rcfile then
          Vernac.load_vernac ~time ~verbosely:false ~interactive:false ~check:true doc sid !rcfile
        else raise (Sys_error ("Cannot read rcfile: "^ !rcfile))
      else
	try
	  let warn x = Feedback.msg_warning (str x) in
	  let inferedrc = List.find CUnix.file_readable_p [
	    Envars.xdg_config_home warn / rcdefaultname^"."^Coq_config.version;
	    Envars.xdg_config_home warn / rcdefaultname;
	    Envars.home ~warn / "."^rcdefaultname^"."^Coq_config.version;
	    Envars.home ~warn / "."^rcdefaultname
	  ] in
          Vernac.load_vernac ~time ~verbosely:false ~interactive:false ~check:true doc sid inferedrc
	with Not_found -> doc, sid
	(*
	Flags.if_verbose
	  mSGNL (str ("No coqrc or coqrc."^Coq_config.version^
			 " found. Skipping rcfile loading."))
	*)
    with reraise ->
      let reraise = CErrors.push reraise in
      let () = Feedback.msg_info (str"Load of rcfile failed.") in
      iraise reraise
  else
    (Flags.if_verbose Feedback.msg_info (str"Skipping rcfile loading.");
     doc, sid)

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

(* Options -I, -I-as, and -R of the command line *)
let includes = ref []
let push_include s alias implicit =
  includes := (s, alias, implicit) :: !includes
let ml_includes = ref []
let push_ml_include s = ml_includes := s :: !ml_includes

let ml_path_if c p =
  let open Mltop in
  let f x = { recursive = false; path_spec = MlPath x } in
  if c then List.map f p else []

(* Initializes the LoadPath *)
let init_load_path ~load_init =
  let open Mltop in
  let coqlib = Envars.coqlib () in
  let user_contrib = coqlib/"user-contrib" in
  let xdg_dirs = Envars.xdg_dirs ~warn:(fun x -> Feedback.msg_warning (str x)) in
  let coqpath = Envars.coqpath in
  let coq_path = Names.DirPath.make [Libnames.coq_root] in

  (* NOTE: These directories are searched from last to first *)
  (* first, developer specific directory to open *)
  ml_path_if Coq_config.local [coqlib/"dev"] @

  (* main loops *)
  ml_path_if (Coq_config.local || !Flags.boot) [coqlib/"stm"; coqlib/"ide"] @
  ml_path_if (System.exists_dir (coqlib/"toploop")) [coqlib/"toploop"] @

  (* then standard library and plugins *)
  [build_stdlib_path ~load_init ~unix_path:(coqlib/"theories") ~coq_path ~with_ml:false;
   build_stdlib_path ~load_init ~unix_path:(coqlib/"plugins")  ~coq_path ~with_ml:true ] @

  (* then user-contrib *)
  (if Sys.file_exists user_contrib then
     [build_userlib_path ~unix_path:user_contrib] else []
  ) @

  (* then directories in XDG_DATA_DIRS and XDG_DATA_HOME and COQPATH *)
  List.map (fun s -> build_userlib_path ~unix_path:s) (xdg_dirs @ coqpath) @

  (* then current directory (not recursively!) *)
  [ { recursive = false;
      path_spec = VoPath { unix_path = ".";
                           coq_path = Libnames.default_root_prefix;
                           implicit = false;
                           has_ml = AddTopML }
    } ] @

  (* additional loadpaths, given with options -Q and -R *)
  List.map
    (fun (unix_path, coq_path, implicit) ->
       { recursive = true;
         path_spec = VoPath { unix_path; coq_path; has_ml = Mltop.AddNoML; implicit } })
      (List.rev !includes) @

  (* additional ml directories, given with option -I *)
  List.map (fun s -> {recursive = false; path_spec = MlPath s}) (List.rev !ml_includes)

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
