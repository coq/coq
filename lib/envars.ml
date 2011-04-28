(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This file gathers environment variables needed by Coq to run (such
   as coqlib) *)

let coqbin () =
  if !Flags.boot || Coq_config.local
  then Filename.concat Coq_config.coqsrc "bin"
  else System.canonical_path_name (Filename.dirname Sys.executable_name)

(* On win32, we add coqbin to the PATH at launch-time (this used to be
   done in a .bat script). *)

let _ =
  if Coq_config.arch = "win32" then
    Unix.putenv "PATH" (coqbin() ^ ";" ^ System.getenv_else "PATH" "")

let reldir instdir testfile oth =
  let prefix = Filename.dirname (coqbin ()) in
  let rpath = if Coq_config.local then [] else instdir in
  let out = List.fold_left Filename.concat prefix rpath in
  if Sys.file_exists (Filename.concat out testfile) then out else oth

let guess_coqlib () =
  let file = "states/initial.coq" in
    if Sys.file_exists (Filename.concat Coq_config.coqlib file)
    then Coq_config.coqlib
    else reldir (if Coq_config.arch = "win32" then ["lib"] else ["lib";"coq"]) file
      (Util.error "cannot guess a path for Coq libraries; please use -coqlib option")

let coqlib () =
  if !Flags.coqlib_spec then !Flags.coqlib else
    (if !Flags.boot then Coq_config.coqsrc else guess_coqlib ())

let docdir () =
  reldir (if Coq_config.arch = "win32" then ["doc"] else ["share";"doc";"coq"]) "html" Coq_config.docdir

let path_to_list p =
  let sep = if Sys.os_type = "Win32" then ';' else ':' in
    Util.split_string_at sep p

let coqpath () =
  try
    let path = Sys.getenv "COQPATH" in
      List.rev (path_to_list path)
  with _ -> []

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

(* TODO : essayer aussi camlbin *)
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


