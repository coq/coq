(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This file gathers environment variables needed by Coq to run (such
   as coqlib) *)

let coqbin =
  System.canonical_path_name (Filename.dirname Sys.executable_name)

(* The following only makes sense when executables are running from
   source tree (e.g. during build or in local mode). *)
let coqroot = Filename.dirname coqbin

(* On win32, we add coqbin to the PATH at launch-time (this used to be
   done in a .bat script). *)

let _ =
  if Coq_config.arch = "win32" then
    Unix.putenv "PATH" (coqbin ^ ";" ^ System.getenv_else "PATH" "")

let reldir instdir testfile oth =
  let rpath = if Coq_config.local then [] else instdir in
  let out = List.fold_left Filename.concat coqroot rpath in
  if Sys.file_exists (Filename.concat out testfile) then out else oth ()

let guess_coqlib () =
  let file = "states/initial.coq" in
    reldir (if Coq_config.arch = "win32" then ["lib"] else ["lib";"coq"]) file
      (fun () ->
        let coqlib = match Coq_config.coqlib with
          | Some coqlib -> coqlib
          | None -> coqroot
        in
        if Sys.file_exists (Filename.concat coqlib file)
        then coqlib
        else Util.error "cannot guess a path for Coq libraries; please use -coqlib option")

let coqlib () =
  if !Flags.coqlib_spec then !Flags.coqlib else
    (if !Flags.boot then coqroot else guess_coqlib ())

let docdir () =
  reldir (if Coq_config.arch = "win32" then ["doc"] else ["share";"doc";"coq"]) "html" (fun () -> Coq_config.docdir)

let path_to_list p =
  let sep = if Sys.os_type = "Win32" then ';' else ':' in
    Util.split_string_at sep p

let xdg_data_home =
  Filename.concat
    (System.getenv_else "XDG_DATA_HOME" (Filename.concat System.home ".local/share"))
    "coq"

let xdg_config_home =
  Filename.concat
    (System.getenv_else "XDG_CONFIG_HOME" (Filename.concat System.home ".config"))
    "coq"

let xdg_data_dirs =
  try
    List.map (fun dir -> Filename.concat dir "coq") (path_to_list (Sys.getenv "XDG_DATA_DIRS"))
  with Not_found -> [ "/usr/local/share/coq"; "/usr/share/coq" ]

let xdg_dirs =
  let dirs = xdg_data_home :: xdg_data_dirs
  in
  List.rev (List.filter Sys.file_exists dirs)

let coqpath =
  try
    let path = Sys.getenv "COQPATH" in
      List.rev (List.filter Sys.file_exists (path_to_list path))
  with Not_found -> []

let rec which l f =
  match l with
    | [] -> raise Not_found
    | p :: tl ->
	if Sys.file_exists (Filename.concat p f)
	then p
	else which tl f

let guess_camlbin () =
  let path = try Sys.getenv "PATH" with _ -> raise Not_found in
  let lpath = path_to_list path in
    which lpath "ocamlc"

let guess_camlp4bin () =
  let path = try Sys.getenv "PATH" with _ -> raise Not_found in
  let lpath = path_to_list path in
    which lpath Coq_config.camlp4

let camlbin () =
  if !Flags.camlbin_spec then !Flags.camlbin else
    if !Flags.boot then Coq_config.camlbin else
      try guess_camlbin () with _ -> Coq_config.camlbin

let camllib () =
  if !Flags.boot
  then Coq_config.camllib
  else
    let camlbin = camlbin () in
    let com = (Filename.concat camlbin "ocamlc") ^ " -where" in
    let _,res = System.run_command (fun x -> x) (fun _ -> ()) com in
    Util.strip res

let camlp4bin () =
  if !Flags.camlp4bin_spec then !Flags.camlp4bin else
    if !Flags.boot then Coq_config.camlp4bin else
      try guess_camlp4bin () with _ -> let cb = camlbin () in
				       if Sys.file_exists (Filename.concat cb Coq_config.camlp4) then cb
				       else Coq_config.camlp4bin

let camlp4lib () =
  if !Flags.boot
  then Coq_config.camlp4lib
  else
    let camlp4bin = camlp4bin () in
    let com = (Filename.concat camlp4bin Coq_config.camlp4) ^ " -where" in
    let _,res = System.run_command (fun x -> x) (fun _ -> ()) com in
    Util.strip res


