
(* $Id$ *)

open Pp
open System
open Toplevel

let set_debug () = Options.debug := true

(* Load of rcfile.
 * rcfile is either $HOME/.coqrc.VERSION, or $HOME/.coqrc if the first one
 * does not exist. *)

let rcfile = ref (Filename.concat home ".coqrc")
let rcfile_specified = ref false
let set_rcfile s = rcfile := s; rcfile_specified := true
let set_rcuser s = rcfile := Filename.concat ("~"^s) ".coqrc"

let load_rc = ref true
let no_load_rc () = load_rc := false

let load_rcfile() =
  if !load_rc then
    try
      if !rcfile_specified then
        if file_readable_p !rcfile then 
          Vernac.load_vernac false !rcfile
        else raise (Sys_error ("Cannot read rcfile: "^ !rcfile))
      else if file_readable_p (!rcfile^"."^Coq_config.version) then
        Vernac.load_vernac false (!rcfile^"."^Coq_config.version)
      else if file_readable_p !rcfile then
        Vernac.load_vernac false !rcfile
      else mSGNL [< 'sTR ("No .coqrc or .coqrc."^Coq_config.version^
		   " found. Skipping rcfile loading.") >]
    with e ->
      (mSGNL [< 'sTR"Load of rcfile failed." >];
       raise e)
  else mSGNL [< 'sTR"Skipping rcfile loading." >]

(*Puts dir in the path of ML and in the LoadPath*)
let add_include s =
  Mltop.dir_ml_dir s;
  add_path s

(*By the option -include -I or -R of the command line*)
let includes = ref []
let push_include s = includes := s :: !includes
let rec_include s = includes := (all_subdirs s)@(!includes)

(*Because find puts "./" and the loadpath is not really pretty-printed*)
let hm2 str=
  String.sub str 2 ((String.length str)-2)

(*Initializes the LoadPath according to COQLIB and Coq_config*)
let init_load_path () =
  (* default load path; only if COQLIB is defined *)
  begin
    try
      let coqlib = Sys.getenv "COQLIB" in
      if coqlib <> "" then
      	List.iter
	  (fun s -> add_include (Filename.concat coqlib s))
      	  ("states" :: 
	   (List.map (fun s -> Filename.concat "theories" (hm2 s))
             Coq_config.theories_dirs))
    with Not_found -> ()
  end ;

  begin
    try
      let camlp4 = Sys.getenv "CAMLP4LIB" in add_include camlp4
    with Not_found -> ()
  end ;

  add_include "." ;

  (* additional loadpath, given with -I -include -R options *)
  List.iter add_include (List.rev !includes);
  includes := []
