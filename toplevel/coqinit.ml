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
let add_stdlib_path ~load_init ~unix_path ~coq_root ~with_ml =
  let add_ml = if with_ml then Mltop.AddRecML else Mltop.AddNoML in
  Mltop.add_rec_path add_ml ~unix_path ~coq_root ~implicit:load_init

let add_userlib_path ~unix_path =
  Mltop.add_rec_path Mltop.AddRecML ~unix_path
    ~coq_root:Libnames.default_root_prefix ~implicit:false

(* Options -I, -I-as, and -R of the command line *)
let includes = ref []
let push_include s alias implicit =
  includes := (s, alias, implicit) :: !includes
let ml_includes = ref []
let push_ml_include s = ml_includes := s :: !ml_includes

(* Initializes the LoadPath *)
let init_load_path ~load_init =
  let coqlib = Envars.coqlib () in
  let user_contrib = coqlib/"user-contrib" in
  let xdg_dirs = Envars.xdg_dirs ~warn:(fun x -> Feedback.msg_warning (str x)) in
  let coqpath = Envars.coqpath in
  let coq_root = Names.DirPath.make [Libnames.coq_root] in
    (* NOTE: These directories are searched from last to first *)
    (* first, developer specific directory to open *)
    if Coq_config.local then
      Mltop.add_ml_dir (coqlib/"dev");
    (* main loops *)
    if Coq_config.local || !Flags.boot then begin
      Mltop.add_ml_dir (coqlib/"stm");
      Mltop.add_ml_dir (coqlib/"ide")
    end;
    if System.exists_dir (coqlib/"toploop") then
      Mltop.add_ml_dir (coqlib/"toploop");
    (* then standard library *)
    add_stdlib_path ~load_init ~unix_path:(coqlib/"theories") ~coq_root ~with_ml:false;
    (* then plugins *)
    add_stdlib_path ~load_init ~unix_path:(coqlib/"plugins") ~coq_root ~with_ml:true;
    (* then user-contrib *)
    if Sys.file_exists user_contrib then
      add_userlib_path ~unix_path:user_contrib;
    (* then directories in XDG_DATA_DIRS and XDG_DATA_HOME *)
    List.iter (fun s -> add_userlib_path ~unix_path:s) xdg_dirs;
    (* then directories in COQPATH *)
    List.iter (fun s -> add_userlib_path ~unix_path:s) coqpath;
    (* then current directory (not recursively!) *)
    Mltop.add_ml_dir ".";
    Loadpath.add_load_path "." Libnames.default_root_prefix ~implicit:false;
    (* additional loadpath, given with options -Q and -R *)
    List.iter
      (fun (unix_path, coq_root, implicit) ->
        Mltop.add_rec_path Mltop.AddNoML ~unix_path ~coq_root ~implicit)
      (List.rev !includes);
    (* additional ml directories, given with option -I *)
    List.iter Mltop.add_ml_dir (List.rev !ml_includes)

(* Initialises the Ocaml toplevel before launching it, so that it can
   find the "include" file in the *source* directory *)
let init_ocaml_path () =
  let add_subdir dl =
    Mltop.add_ml_dir (List.fold_left (/) Envars.coqroot [dl])
  in
    Mltop.add_ml_dir (Envars.coqlib ());
    List.iter add_subdir Coq_config.all_src_dirs
