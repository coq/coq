(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Files and load path. *)

type physical_path = string
type load_path = physical_path list

let physical_path_of_string s = s
let string_of_physical_path p = p

let path_to_list p =
  let sep = Str.regexp (if Sys.os_type = "Win32" then ";" else ":") in
    Str.split sep p

(* Hints to partially detects if two paths refer to the same repertory *)
let rec remove_path_dot p =
  let curdir = Filename.concat Filename.current_dir_name "" in (* Unix: "./" *)
  let n = String.length curdir in
  let l = String.length p in
  if l > n && String.sub p 0 n = curdir then
    let n' =
      let sl = String.length Filename.dir_sep in
      let i = ref n in
	while !i <= l - sl && String.sub p !i sl = Filename.dir_sep do i := !i + sl done; !i in
    remove_path_dot (String.sub p n' (l - n'))
  else
    p

let strip_path p =
  let cwd = Filename.concat (Sys.getcwd ()) "" in (* Unix: "`pwd`/" *)
  let n = String.length cwd in
  let l = String.length p in
  if l > n && String.sub p 0 n = cwd then
    let n' =
      let sl = String.length Filename.dir_sep in
      let i = ref n in
	while !i <= l - sl && String.sub p !i sl = Filename.dir_sep do i := !i + sl done; !i in
    remove_path_dot (String.sub p n' (l - n'))
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

let correct_path f dir = if Filename.is_relative f then Filename.concat dir f else f

let file_readable_p name =
  try Unix.access name [Unix.R_OK];true with Unix.Unix_error (_, _, _) -> false

let run_command converter f c =
  let result = Buffer.create 127 in
  let cin,cout,cerr = Unix.open_process_full c (Unix.environment ()) in
  let buff = String.make 127 ' ' in
  let buffe = String.make 127 ' ' in
  let n = ref 0 in
  let ne = ref 0 in

  while n:= input cin buff 0 127 ; ne := input cerr buffe 0 127 ;
    !n+ !ne <> 0
  do
    let r = converter (String.sub buff 0 !n) in
    f r;
    Buffer.add_string result r;
    let r = converter (String.sub buffe 0 !ne) in
    f r;
    Buffer.add_string result r
  done;
  (Unix.close_process_full (cin,cout,cerr),  Buffer.contents result)

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
