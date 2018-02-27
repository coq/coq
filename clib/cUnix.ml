(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Files and load path. *)

type physical_path = string
type load_path = physical_path list

let physical_path_of_string s = s
let string_of_physical_path p = p

let escaped_string_of_physical_path p =
  (* We assume a reasonable-enough path (typically utf8) and prevents
     the presence of space; other escapings might be useful... *)
  if String.contains p ' ' then "\"" ^ p ^ "\"" else p

let path_to_list p =
  let sep = Str.regexp (if Sys.os_type = "Win32" then ";" else ":") in
    Str.split sep p

(* Some static definitions concerning filenames *)

let dirsep = Filename.dir_sep (* Unix: "/" *)
let dirsep_len = String.length dirsep
let curdir = Filename.concat Filename.current_dir_name "" (* Unix: "./" *)
let curdir_len = String.length curdir

(* Hints to partially detects if two paths refer to the same directory *)

(** cut path [p] after all the [/] that come at position [pos]. *)
let rec cut_after_dirsep p pos =
  if CString.is_sub dirsep p pos then
    cut_after_dirsep p (pos + dirsep_len)
  else
    String.sub p pos (String.length p - pos)

(** remove all initial "./" in a path unless the path is exactly "./" *)
let rec remove_path_dot p =
  if CString.is_sub curdir p 0 then
    if String.length p = curdir_len
    then Filename.current_dir_name
    else remove_path_dot (cut_after_dirsep p curdir_len)
  else
    p

(** If a path [p] starts with the current directory $PWD then
    [strip_path p] returns the sub-path relative to $PWD.
    Any leading "./" are also removed from the result. *)
let strip_path p =
  let cwd = Filename.concat (Sys.getcwd ()) "" in (* Unix: "`pwd`/" *)
  if CString.is_sub cwd p 0 then
    remove_path_dot (cut_after_dirsep p (String.length cwd))
  else
    remove_path_dot p

let canonical_path_name p =
  let current = Sys.getcwd () in
  try
    Sys.chdir p;
    let p' = Sys.getcwd () in
    Sys.chdir current;
    p'
  with Sys_error _ ->
    (* We give up to find a canonical name and just simplify it... *)
    strip_path p

let make_suffix name suffix =
  if Filename.check_suffix name suffix then name else (name ^ suffix)

let get_extension f =
  let pos = try String.rindex f '.' with Not_found -> String.length f in
  String.sub f pos (String.length f - pos)

let correct_path f dir =
  if Filename.is_relative f then Filename.concat dir f else f

let file_readable_p name =
  try Unix.access name [Unix.R_OK];true
  with Unix.Unix_error (_, _, _) -> false

(* As for [Unix.close_process], a [Unix.waipid] that ignores all [EINTR] *)

let rec waitpid_non_intr pid =
  try snd (Unix.waitpid [] pid)
  with Unix.Unix_error (Unix.EINTR, _, _) -> waitpid_non_intr pid

(** [run_command com] launches command [com] (via /bin/sh),
    and returns the contents of stdout and stderr. If given, [~hook]
    is called on each elements read on stdout or stderr. *)

let run_command ?(hook=(fun _ ->())) c =
  let result = Buffer.create 127 in
  let cin,cout,cerr = Unix.open_process_full c (Unix.environment ()) in
  let buff = Bytes.make 127 ' ' in
  let buffe = Bytes.make 127 ' ' in
  let n = ref 0 in
  let ne = ref 0 in
  while n:= input cin buff 0 127 ; ne := input cerr buffe 0 127 ;
    !n+ !ne <> 0
  do
    let r = Bytes.sub buff 0 !n in (hook r; Buffer.add_bytes result r);
    let r = Bytes.sub buffe 0 !ne in (hook r; Buffer.add_bytes result r);
  done;
  (Unix.close_process_full (cin,cout,cerr),  Buffer.contents result)

(** [sys_command] launches program [prog] with arguments [args].
    It behaves like [Sys.command], except that we rely on
    [Unix.create_process], it's hardly more complex and avoids dealing
    with shells. In particular, no need to quote arguments
    (against whitespace or other funny chars in paths), hence no need
    to care about the different quoting conventions of /bin/sh and cmd.exe. *)

let sys_command prog args =
  let argv = Array.of_list (prog::args) in
  let pid = Unix.create_process prog argv Unix.stdin Unix.stdout Unix.stderr in
  waitpid_non_intr pid

(*
  checks if two file names refer to the same (existing) file by
  comparing their device and inode.
  It seems that under Windows, inode is always 0, so we cannot
  accurately check if

*)
(* Optimised for partial application (in case many candidates must be
   compared to f1). *)
let same_file f1 =
  try
    let s1 = Unix.stat f1 in
    (fun f2 ->
      try
        let s2 = Unix.stat f2 in
        s1.Unix.st_dev = s2.Unix.st_dev &&
          if Sys.os_type = "Win32" then f1 = f2
          else s1.Unix.st_ino = s2.Unix.st_ino
      with
          Unix.Unix_error _ -> false)
  with
      Unix.Unix_error _ -> (fun _ -> false)
