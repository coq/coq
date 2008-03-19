(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open System
open Toplevel

let (/) = Filename.concat

let set_debug () = Flags.debug := true

(* Loading of the ressource file.
   rcfile is either $HOME/.coqrc.VERSION, or $HOME/.coqrc if the first one
  does not exist. *)

let rcfile = ref (home/".coqrc")
let rcfile_specified = ref false
let set_rcfile s = rcfile := s; rcfile_specified := true
let set_rcuser s = rcfile := ("~"^s)/".coqrc"

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
      else ()
	(*
	Flags.if_verbose
	  mSGNL (str ("No .coqrc or .coqrc."^Coq_config.version^
			 " found. Skipping rcfile loading."))
	*)
    with e ->
      (msgnl (str"Load of rcfile failed.");
       raise e)
  else 
    Flags.if_verbose msgnl (str"Skipping rcfile loading.")

let add_ml_include s =
  Mltop.add_ml_dir s

(* Puts dir in the path of ML and in the LoadPath *)
let coq_add_path s = Mltop.add_path s (Names.make_dirpath [Nameops.coq_root])
let coq_add_rec_path s = Mltop.add_rec_path s (Names.make_dirpath [Nameops.coq_root])

(* By the option -include -I or -R of the command line *)
let includes = ref []
let push_include (s, alias) = includes := (s,alias,false) :: !includes
let push_rec_include (s, alias) = includes := (s,alias,true) :: !includes

(* Because find puts "./" and the loadpath is not nicely pretty-printed *)
let hm2 s = 
  let n = String.length s in
  if n > 1 && s.[0] = '.' && s.[1] = '/' then String.sub s 2 (n-2) else s

(* The list of all theories in the standard library /!\ order does matter *)
let theories_dirs_map = [
    "theories/Unicode", "Unicode" ;
    "theories/Classes", "Classes" ; 
    "theories/Program", "Program" ; 
    "theories/FSets", "FSets" ; 
    "theories/Reals", "Reals" ; 
    "theories/Strings", "Strings" ; 
    "theories/Sorting", "Sorting" ; 
    "theories/Setoids", "Setoids" ; 
    "theories/Sets", "Sets" ; 
    "theories/Lists", "Lists" ; 
    "theories/Wellfounded", "Wellfounded" ; 
    "theories/Relations", "Relations" ; 
    "theories/Ints", "Ints" ; 
    "theories/Numbers", "Numbers" ; 
    "theories/QArith", "QArith" ; 
    "theories/NArith", "NArith" ; 
    "theories/ZArith", "ZArith" ; 
    "theories/Arith", "Arith" ; 
    "theories/Bool", "Bool" ; 
    "theories/Logic", "Logic" ; 
    "theories/Init", "Init"
  ]

(* Initializes the LoadPath according to COQLIB and Coq_config *)
let init_load_path () =
  (* developper specific directories to open *)
  let dev = if Coq_config.local then [ "dev" ] else [] in
  let coqlib =
    (* variable COQLIB overrides the default library *)
    getenv_else "COQLIB"
      (if Coq_config.local || !Flags.boot then Coq_config.coqtop
	else Coq_config.coqlib) in
  let user_contrib = coqlib/"user-contrib" in
  let dirs = "states" :: "contrib" :: dev in
  let camlp4 = getenv_else "CAMLP4LIB" Coq_config.camlp4lib in
    (* first user-contrib *)
    if Sys.file_exists user_contrib then 
      Mltop.add_rec_path user_contrib Nameops.default_root_prefix;
    (* then states, contrib and dev *)
    List.iter (fun s -> coq_add_rec_path (coqlib/s)) dirs;
    (* then standard library *)
    List.iter 
      (fun (s,alias) -> Mltop.add_rec_path (coqlib/s) (Names.make_dirpath [Names.id_of_string alias; Nameops.coq_root])) 
      theories_dirs_map;
    (* then camlp4lib *)
    add_ml_include camlp4;
    (* then current directory *)
    Mltop.add_path "." Nameops.default_root_prefix;
    (* additional loadpath, given with -I -include -R options *)
    List.iter 
      (fun (s,alias,reci) ->
	if reci then Mltop.add_rec_path s alias else Mltop.add_path s alias)
      (List.rev !includes)
      
let init_library_roots () =
  includes := []

(* Initialises the Ocaml toplevel before launching it, so that it can
   find the "include" file in the *source* directory *)
(* We only assume that the variable COQTOP is set *)
let init_ocaml_path () =
  let coqtop = getenv_else "COQTOP" Coq_config.coqtop in
  let add_subdir dl = 
    Mltop.add_ml_dir (List.fold_left (/) coqtop dl) 
  in
  List.iter add_subdir
    [ [ "config" ]; [ "dev" ]; [ "lib" ]; [ "kernel" ]; [ "library" ]; 
      [ "pretyping" ]; [ "interp" ]; [ "parsing" ]; [ "proofs" ];
      [ "tactics" ]; [ "toplevel" ]; [ "translate" ]; [ "ide" ] ]
