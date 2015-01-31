(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Unix

type unix_path = string (* path in unix-style, with '/' separator *)

type file_kind =
  | FileDir of unix_path * (* basename of path: *) string 
  | FileRegular of string (* basename of file *)

(* Copy of Filename.concat but assuming paths to always be POSIX *)

let (//) dirname filename =
  let l = String.length dirname in
  if l = 0 || dirname.[l-1] = '/'
  then dirname ^ filename
  else dirname ^ "/" ^ filename

(* Excluding directories; We avoid directories starting with . as well
   as CVS and _darcs and any subdirs given via -exclude-dir *)

let skipped_dirnames = ref ["CVS"; "_darcs"]

let exclude_directory f = skipped_dirnames := f :: !skipped_dirnames

let ok_dirname f =
  not (f = "") && f.[0] != '.' &&
  not (List.mem f !skipped_dirnames) (*&&
  (match Unicode.ident_refutation f with None -> true | _ -> false)*)

(* Check directory can be opened *)

let exists_dir dir =
  try let _ = closedir (opendir dir) in true with Unix_error _ -> false

let check_unix_dir warn dir =
  if (Sys.os_type = "Win32" || Sys.os_type = "Cygwin") &&
    (String.length dir > 2 && dir.[1] = ':' ||
     String.contains dir '\\' ||
     String.contains dir ';')
  then warn ("assuming " ^ dir ^
             " to be a Unix path even if looking like a Win32 path.")

let apply_subdir f path name =
  (* we avoid all files and subdirs starting by '.' (e.g. .svn) *)
  (* as well as skipped files like CVS, ... *)
  if name.[0] <> '.' && ok_dirname name then
    let path = if path = "." then name else path//name in
    match try (stat path).st_kind with Unix_error _ -> S_BLK with
    | S_DIR -> f (FileDir (path,name))
    | S_REG -> f (FileRegular name)
    | _ -> ()

let process_directory f path =
  let dirh = opendir path in
  try while true do apply_subdir f path (readdir dirh) done
  with End_of_file -> closedir dirh

let process_subdirectories f path =
  let f = function FileDir (path,base) -> f path base | FileRegular _ -> () in
  process_directory f path

