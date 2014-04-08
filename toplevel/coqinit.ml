(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
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

let load_rcfile() =
  if !load_rc then
    try
      if !rcfile_specified then
        if CUnix.file_readable_p !rcfile then
          Vernac.load_vernac false !rcfile
        else raise (Sys_error ("Cannot read rcfile: "^ !rcfile))
      else
	try
	  let warn x = msg_warning (str x) in
	  let inferedrc = List.find CUnix.file_readable_p [
	    Envars.xdg_config_home warn / rcdefaultname^"."^Coq_config.version;
	    Envars.xdg_config_home warn / rcdefaultname;
	    Envars.home ~warn / "."^rcdefaultname^"."^Coq_config.version;
	    Envars.home ~warn / "."^rcdefaultname
	  ] in
          Vernac.load_vernac false inferedrc
	with Not_found -> ()
	(*
	Flags.if_verbose
	  mSGNL (str ("No coqrc or coqrc."^Coq_config.version^
			 " found. Skipping rcfile loading."))
	*)
    with reraise ->
      let reraise = Errors.push reraise in
      let () = msg_info (str"Load of rcfile failed.") in
      raise reraise
  else
    Flags.if_verbose msg_info (str"Skipping rcfile loading.")

(* Puts dir in the path of ML and in the LoadPath *)
let coq_add_path unix_path s =
  Mltop.add_path ~unix_path ~coq_root:(Names.DirPath.make [Nameops.coq_root;Names.Id.of_string s]) ~implicit:true;
  Mltop.add_ml_dir unix_path

(* Recursively puts dir in the LoadPath if -nois was not passed *)
let add_stdlib_path ~unix_path ~coq_root ~with_ml =
  if !Flags.load_init then
    Mltop.add_rec_path ~unix_path ~coq_root ~implicit:true
  else
    Mltop.add_path ~unix_path ~coq_root ~implicit:false;
  if with_ml then
    Mltop.add_rec_ml_dir unix_path

let add_userlib_path ~unix_path =
  Mltop.add_path ~unix_path ~coq_root:Nameops.default_root_prefix ~implicit:false;
  Mltop.add_rec_ml_dir unix_path

(* Options -I, -I-as, and -R of the command line *)
let includes = ref []
let push_include s alias recursive implicit =
  includes := (s,alias,recursive,implicit) :: !includes
let ml_includes = ref []
let push_ml_include s = ml_includes := s :: !ml_includes

(* Initializes the LoadPath *)
let init_load_path () =
  let coqlib = Envars.coqlib () in
  let user_contrib = coqlib/"user-contrib" in
  let xdg_dirs = Envars.xdg_dirs ~warn:(fun x -> msg_warning (str x)) in
  let coqpath = Envars.coqpath in
  let coq_root = Names.DirPath.make [Nameops.coq_root] in
    (* NOTE: These directories are searched from last to first *)
    (* first, developer specific directory to open *)
    if Coq_config.local then coq_add_path (coqlib/"dev") "dev";
    (* then standard library *)
    add_stdlib_path ~unix_path:(coqlib/"theories") ~coq_root ~with_ml:false;
    (* then plugins *)
    add_stdlib_path ~unix_path:(coqlib/"plugins") ~coq_root ~with_ml:true;
    (* then user-contrib *)
    if Sys.file_exists user_contrib then
      add_userlib_path ~unix_path:user_contrib;
    (* then directories in XDG_DATA_DIRS and XDG_DATA_HOME *)
    List.iter (fun s -> add_userlib_path ~unix_path:s) xdg_dirs;
    (* then directories in COQPATH *)
    List.iter (fun s -> add_userlib_path ~unix_path:s) coqpath;
    (* then current directory *)
    Mltop.add_path ~unix_path:"." ~coq_root:Nameops.default_root_prefix ~implicit:false;
    (* additional loadpath, given with options -I-as, -Q, and -R *)
    List.iter
      (fun (unix_path, coq_root, reci, implicit) ->
        (if reci then Mltop.add_rec_path else Mltop.add_path)
          ~unix_path ~coq_root ~implicit)
      (List.rev !includes);
    (* additional ml directories, given with option -I *)
    List.iter Mltop.add_ml_dir (List.rev !ml_includes)

let init_library_roots () =
  includes := []

(* Initialises the Ocaml toplevel before launching it, so that it can
   find the "include" file in the *source* directory *)
let init_ocaml_path () =
  let add_subdir dl =
    Mltop.add_ml_dir (List.fold_left (/) Envars.coqroot dl)
  in
    Mltop.add_ml_dir (Envars.coqlib ());
    List.iter add_subdir
      [ [ "config" ]; [ "dev" ]; [ "lib" ]; [ "kernel" ]; [ "library" ];
	[ "pretyping" ]; [ "interp" ]; [ "parsing" ]; [ "proofs" ];
	[ "tactics" ]; [ "toplevel" ]; [ "printing" ]; [ "intf" ];
        [ "grammar" ]; [ "ide" ] ]

let get_compat_version = function
  | "8.3" -> Flags.V8_3
  | "8.2" -> Flags.V8_2
  | ("8.1" | "8.0") as s ->
    msg_warning (strbrk ("Compatibility with version "^s^" not supported."));
    Flags.V8_2
  | s -> Errors.error ("Unknown compatibility version \""^s^"\".")
