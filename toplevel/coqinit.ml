
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
      else 
	if Options.is_verbose() then 
	  mSGNL [< 'sTR ("No .coqrc or .coqrc."^Coq_config.version^
			 " found. Skipping rcfile loading.") >]
    with e ->
      (mSGNL [< 'sTR"Load of rcfile failed." >];
       raise e)
  else 
    if Options.is_verbose() then mSGNL [< 'sTR"Skipping rcfile loading." >]

(* Puts dir in the path of ML and in the LoadPath *)
let add_include s =
  Mltop.dir_ml_dir s;
  add_path s

(* By the option -include -I or -R of the command line *)
let includes = ref []
let push_include s = includes := s :: !includes
let rec_include s = includes := (all_subdirs s) @ !includes

(* Because find puts "./" and the loadpath is not nicely pretty-printed *)
let hm2 s = 
  let n = String.length s in
  if n > 1 && s.[0] = '.' && s.[1] = '/' then String.sub s 2 (n-2) else s

let getenv_else s dft = try Sys.getenv s with Not_found -> dft

(* Initializes the LoadPath according to COQLIB and Coq_config *)
let init_load_path () =
  if Coq_config.local then
    (* local use (no installation) *)
    List.iter 
      (fun s -> add_include (Filename.concat Coq_config.coqtop s))
      ("states" :: "dev" ::
       (List.map 
	  (fun s -> Filename.concat "theories" (hm2 s))
          Coq_config.theories_dirs))
  else begin
    (* default load path; only if COQLIB is defined *)
    let coqlib = getenv_else "COQLIB" Coq_config.coqlib in
    add_include coqlib
  end;
  let camlp4 = getenv_else "CAMLP4LIB" Coq_config.camlp4lib in
  add_include camlp4;
  add_include ".";
  (* additional loadpath, given with -I -include -R options *)
  List.iter add_include (List.rev !includes);
  includes := []
