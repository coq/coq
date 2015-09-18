(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util

(** {1 Helper functions} *)

let getenv_else s dft = try Sys.getenv s with Not_found -> dft ()

let safe_getenv warning n =
  getenv_else n (fun () ->
    warning ("Environment variable "^n^" not found: using '$"^n^"' .");
    ("$"^n)
  )

let ( / ) a b =
  if Filename.is_relative b then a ^ "/" ^ b else b

let coqify d = d / "coq"

let opt2list = function None -> [] | Some x -> [x]

let home ~warn =
  getenv_else "HOME" (fun () ->
    try (Sys.getenv "HOMEDRIVE")^(Sys.getenv "HOMEPATH") with Not_found ->
      getenv_else "USERPROFILE" (fun () ->
	warn ("Cannot determine user home directory, using '.' .");
	Filename.current_dir_name))

let path_to_list p =
  let sep = if String.equal Sys.os_type "Win32" then ';' else ':' in
    String.split sep p

let user_path () =
  path_to_list (Sys.getenv "PATH") (* may raise Not_found *)

let rec which l f =
  match l with
    | [] ->
      raise Not_found
    | p :: tl ->
      if Sys.file_exists (p / f) then
	p
      else
	which tl f

let expand_path_macros ~warn s =
  let rec expand_atom s i =
    let l = String.length s in
    if i<l && (Util.is_digit s.[i] || Util.is_letter s.[i] || s.[i] == '_')
    then expand_atom s (i+1)
    else i in
  let rec expand_macros s i =
    let l = String.length s in
    if Int.equal i l then s else
      match s.[i] with
	| '$' ->
	  let n = expand_atom s (i+1) in
	  let v = safe_getenv warn (String.sub s (i+1) (n-i-1)) in
	  let s = (String.sub s 0 i)^v^(String.sub s n (l-n)) in
	  expand_macros s (i + String.length v)
	| '~' when Int.equal i 0 ->
	  let n = expand_atom s (i+1) in
	  let v =
	    if Int.equal n (i + 1) then home ~warn
	    else (Unix.getpwnam (String.sub s (i+1) (n-i-1))).Unix.pw_dir
	  in
	  let s = v^(String.sub s n (l-n)) in
	  expand_macros s (String.length v)
	| c -> expand_macros s (i+1)
  in expand_macros s 0

(** {1 Paths} *)

(** {2 Coq paths} *)

let relative_base =
  Filename.dirname (Filename.dirname Sys.executable_name)

let coqbin =
  CUnix.canonical_path_name (Filename.dirname Sys.executable_name)

(** The following only makes sense when executables are running from
    source tree (e.g. during build or in local mode). *)
let coqroot =
  Filename.dirname coqbin

(** On win32, we add coqbin to the PATH at launch-time (this used to be
    done in a .bat script). *)
let _ =
  if Coq_config.arch_is_win32 then
    Unix.putenv "PATH" (coqbin ^ ";" ^ getenv_else "PATH" (fun () -> ""))

(** [check_file_else ~dir ~file oth] checks if [file] exists in
    the installation directory [dir] given relatively to [coqroot].
    If this Coq is only locally built, then [file] must be in [coqroot].
    If the check fails, then [oth ()] is evaluated. *)
let check_file_else ~dir ~file oth =
  let path = if Coq_config.local then coqroot else coqroot / dir in
  if Sys.file_exists (path / file) then path else oth ()

let guess_coqlib fail =
  let prelude = "theories/Init/Prelude.vo" in
  let dir = if Coq_config.arch_is_win32 then "lib" else "lib/coq" in
  check_file_else ~dir ~file:prelude
    (fun () ->
      let coqlib = match Coq_config.coqlib with
        | Some coqlib -> coqlib
        | None -> coqroot
      in
      if Sys.file_exists (coqlib / prelude) then coqlib
      else
        fail "cannot guess a path for Coq libraries; please use -coqlib option")

(** coqlib is now computed once during coqtop initialization *)

let set_coqlib ~fail =
  if not !Flags.coqlib_spec then
    let lib = if !Flags.boot then coqroot else guess_coqlib fail in
    Flags.coqlib := lib

let coqlib () = !Flags.coqlib

let docdir () =
  let dir = if Coq_config.arch_is_win32 then "doc" else "share/doc/coq" in
  check_file_else ~dir ~file:"html" (fun () -> Coq_config.docdir)

let coqpath =
  let coqpath = getenv_else "COQPATH" (fun () -> "") in
  let make_search_path path =
    let paths = path_to_list path in
    let valid_paths = List.filter Sys.file_exists paths in
    List.rev valid_paths
  in
  make_search_path coqpath

(** {2 Caml paths} *)

let exe s = s ^ Coq_config.exec_extension

let guess_camlbin () = which (user_path ()) (exe "ocamlc")

let camlbin () =
  if !Flags.camlbin_spec then !Flags.camlbin else
    if !Flags.boot then Coq_config.camlbin else
      try guess_camlbin () with Not_found -> Coq_config.camlbin

let ocamlc () = camlbin () / Coq_config.ocamlc

let ocamlopt () = camlbin () / Coq_config.ocamlopt

let camllib () =
  if !Flags.boot then
    Coq_config.camllib
  else
    let _, res = CUnix.run_command (ocamlc () ^ " -where") in
    String.strip res

(** {2 Camlp4 paths} *)

let guess_camlp4bin () = which (user_path ()) (exe Coq_config.camlp4)

let camlp4bin () =
  if !Flags.camlp4bin_spec then !Flags.camlp4bin else
    if !Flags.boot then Coq_config.camlp4bin else
      try guess_camlp4bin ()
      with Not_found ->
        let cb = camlbin () in
        if Sys.file_exists (cb / exe Coq_config.camlp4) then cb
        else Coq_config.camlp4bin

let camlp4 () = camlp4bin () / exe Coq_config.camlp4

let camlp4lib () =
  if !Flags.boot then
    Coq_config.camlp4lib
  else
    let ex, res = CUnix.run_command (camlp4 () ^ " -where") in
    match ex with
      | Unix.WEXITED 0 -> String.strip res
      | _ -> "/dev/null"

(** {1 XDG utilities} *)

let xdg_data_home warn =
  coqify
    (getenv_else "XDG_DATA_HOME" (fun () -> (home ~warn) / ".local/share"))

let xdg_config_home warn =
  coqify
    (getenv_else "XDG_CONFIG_HOME" (fun () -> (home ~warn) / ".config"))

let xdg_data_dirs warn =
  let sys_dirs =
    try
      List.map coqify (path_to_list (Sys.getenv "XDG_DATA_DIRS"))
    with
      | Not_found when String.equal Sys.os_type "Win32" -> [relative_base / "share"]
      | Not_found -> ["/usr/local/share/coq";"/usr/share/coq"]
  in
  xdg_data_home warn :: sys_dirs @ opt2list Coq_config.datadir

let xdg_config_dirs warn =
  let sys_dirs =
    try
      List.map coqify (path_to_list (Sys.getenv "XDG_CONFIG_DIRS"))
    with
      | Not_found when String.equal Sys.os_type "Win32" -> [relative_base / "config"]
      | Not_found -> ["/etc/xdg/coq"]
  in
  xdg_config_home warn :: sys_dirs @ opt2list Coq_config.configdir

let xdg_dirs ~warn =
  List.filter Sys.file_exists (xdg_data_dirs warn)
