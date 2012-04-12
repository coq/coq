(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Printf
open Coqdep_lexer
open Coqdep_common

(** The basic parts of coqdep (i.e. the parts used by [coqdep -boot])
    are now in [Coqdep_common]. The code that remains here concerns
    the other options. Calling this complete coqdep with the [-boot]
    option should be equivalent to calling [coqdep_boot].
*)

let option_D = ref false
let option_w = ref false
let option_sort = ref false

let rec warning_mult suf iter =
  let tab = Hashtbl.create 151 in
  let check f d =
    begin try
      let d' = Hashtbl.find tab f in
      if (Filename.dirname (file_name f d))
        <> (Filename.dirname (file_name f d')) then begin
	  eprintf "*** Warning : the file %s is defined twice!\n" (f ^ suf);
	  flush stderr
	end
    with Not_found -> () end;
    Hashtbl.add tab f d
  in
  iter check

let add_coqlib_known phys_dir log_dir f =
  match get_extension f [".vo"] with
    | (basename,".vo") ->
        let name = log_dir@[basename] in
	let paths = suffixes name in
        List.iter (fun f -> Hashtbl.add coqlibKnown f ()) paths
    | _ -> ()

let sort () =
  let seen = Hashtbl.create 97 in
  let rec loop file =
    let file = canonize file in
    if not (Hashtbl.mem seen file) then begin
      Hashtbl.add seen file ();
      let cin = open_in (file ^ ".v") in
      let lb = Lexing.from_channel cin in
      try
	while true do
	  match coq_action lb with
	    | Require sl ->
		List.iter
		  (fun s ->
		    try loop (Hashtbl.find vKnown s)
		    with Not_found -> ())
		sl
	    | RequireString s -> loop s
	    | _ -> ()
	done
      with Fin_fichier ->
	close_in cin;
	printf "%s%s " file !suffixe
    end
  in
  List.iter (fun (name,_) -> loop name) !vAccu

let (dep_tab : (string,string list) Hashtbl.t) = Hashtbl.create 151

let mL_dep_list b f =
  try
    Hashtbl.find dep_tab f
  with Not_found ->
    let deja_vu = ref ([] : string list) in
    try
      let chan = open_in f in
      let buf = Lexing.from_channel chan in
      try
	while true do
	  let (Use_module str) = caml_action buf in
	  if str = b then begin
	    eprintf "*** Warning : in file %s the" f;
	    eprintf " notation %s. is useless !\n" b;
	    flush stderr
	  end else
            if not (List.mem str !deja_vu) then addQueue deja_vu str
      	done; []
      with Fin_fichier -> begin
	close_in chan;
	let rl = List.rev !deja_vu in
      	Hashtbl.add dep_tab f rl;
	rl
      end
    with Sys_error _ -> []

let affiche_Declare f dcl =
  printf "\n*** In file %s: \n" f;
  printf "Declare ML Module";
  List.iter (fun str -> printf " \"%s\"" str) dcl;
  printf ".\n";
  flush stdout

let warning_Declare f dcl =
  eprintf "*** Warning : in file %s, the ML modules" f;
  eprintf " declaration should be\n";
  eprintf "*** Declare ML Module";
  List.iter (fun str -> eprintf " \"%s\"" str) dcl;
  eprintf ".\n";
  flush stderr

let traite_Declare f =
  let decl_list = ref ([] : string list) in
  let rec treat = function
    | s :: ll ->
	let s' = basename_noext s in
	(match search_ml_known s with
	   | Some mldir when not (List.mem s' !decl_list) ->
	       let fullname = file_name (String.uncapitalize s') mldir in
	       let depl = mL_dep_list s (fullname ^ ".ml") in
	       treat depl;
	       decl_list := s :: !decl_list
	   | _ -> ());
	treat ll
    | [] -> ()
  in
    try
      let chan = open_in f in
      let buf = Lexing.from_channel chan in
	begin try
	    while true do
      	      let tok = coq_action buf in
      		(match tok with
		  | Declare sl ->
		      decl_list := [];
		      treat sl;
		      decl_list := List.rev !decl_list;
		      if !option_D then
			affiche_Declare f !decl_list
		      else if !decl_list <> sl then
			warning_Declare f !decl_list
		  | _ -> ())
	    done
	  with Fin_fichier -> () end;
	close_in chan
    with Sys_error _ -> ()

let declare_dependencies () =
  List.iter
    (fun (name,_) ->
       traite_Declare (name^".v");
       flush stdout)
    (List.rev !vAccu)

let usage () =
  eprintf
  "[ usage: coqdep [-w] [-I dir] [-R dir coqdir] [-coqlib dir] [-c] [-i] [-D] <filename>+ ]\n";
  flush stderr;
  exit 1

let rec parse = function
  | "-c" :: ll -> option_c := true; parse ll
  | "-D" :: ll -> option_D := true; parse ll
  | "-w" :: ll -> option_w := true; parse ll
  | "-boot" :: ll -> Flags.boot := true; parse ll
  | "-sort" :: ll -> option_sort := true; parse ll
  | ("-noglob" | "-no-glob") :: ll -> option_noglob := true; parse ll
  | "-I" :: r :: "-as" :: ln :: ll -> add_dir add_known r [ln]; parse ll
  | "-I" :: r :: "-as" :: [] -> usage ()
  | "-I" :: r :: ll -> add_dir add_known r []; parse ll
  | "-I" :: [] -> usage ()
  | "-R" :: r :: "-as" :: ln :: ll -> add_rec_dir add_known r [ln]; parse ll
  | "-R" :: r :: "-as" :: [] -> usage ()
  | "-R" :: r :: ln :: ll -> add_rec_dir add_known r [ln]; parse ll
  | "-R" :: ([] | [_]) -> usage ()
  | "-coqlib" :: (r :: ll) -> Flags.coqlib_spec := true; Flags.coqlib := r; parse ll
  | "-coqlib" :: [] -> usage ()
  | "-suffix" :: (s :: ll) -> suffixe := s ; parse ll
  | "-suffix" :: [] -> usage ()
  | "-slash" :: ll -> option_slash := true; parse ll
  | ("-h"|"--help"|"-help") :: _ -> usage ()
  | f :: ll -> treat_file None f; parse ll
  | [] -> ()

let coqdep () =
  if Array.length Sys.argv < 2 then usage ();
  parse (List.tl (Array.to_list Sys.argv));
  if not Coq_config.has_natdynlink then option_natdynlk := false;
  (* NOTE: These directories are searched from last to first *)
  if !Flags.boot then begin
    add_rec_dir add_known "theories" ["Coq"];
    add_rec_dir add_known "plugins" ["Coq"]
  end else begin
    let coqlib = Envars.coqlib Errors.error in
    add_rec_dir add_coqlib_known (coqlib//"theories") ["Coq"];
    add_rec_dir add_coqlib_known (coqlib//"plugins") ["Coq"];
    let user = coqlib//"user-contrib" in
    if Sys.file_exists user then add_rec_dir add_coqlib_known user [];
    List.iter (fun s -> add_rec_dir add_coqlib_known s [])
      (Envars.xdg_dirs (fun x -> Pp.msg_warning (Pp.str x)));
    List.iter (fun s -> add_rec_dir add_coqlib_known s []) Envars.coqpath;
  end;
  List.iter (fun (f,d) -> add_mli_known f d) !mliAccu;
  List.iter (fun (f,d) -> add_mllib_known f d) !mllibAccu;
  List.iter (fun (f,_,d) -> add_ml_known f d) !mlAccu;
  warning_mult ".mli" iter_mli_known;
  warning_mult ".ml" iter_ml_known;
  if !option_sort then begin sort (); exit 0 end;
  if !option_c && not !option_D then mL_dependencies ();
  if not !option_D then coq_dependencies ();
  if !option_w || !option_D then declare_dependencies ()

let _ = Printexc.catch coqdep ()
