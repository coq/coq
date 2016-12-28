(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Minisys regroups some code that used to be in System.
    Unlike System, this module has no dependency and could
    be used for initial compilation target such as coqdep_boot.
    The functions here are still available in System thanks to
    an include. For the signature, look at the top of system.mli
*)

(** Dealing with directories *)

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
  try Sys.is_directory dir with Sys_error _ -> false

let apply_subdir f path name =
  (* we avoid all files and subdirs starting by '.' (e.g. .svn) *)
  (* as well as skipped files like CVS, ... *)
  if ok_dirname name then
    let path = if path = "." then name else path//name in
    match try (Unix.stat path).Unix.st_kind with Unix.Unix_error _ -> Unix.S_BLK with
    | Unix.S_DIR -> f (FileDir (path,name))
    | Unix.S_REG -> f (FileRegular name)
    | _ -> ()

let readdir dir = try Sys.readdir dir with any -> [||]

let process_directory f path =
  Array.iter (apply_subdir f path) (readdir path)

let process_subdirectories f path =
  let f = function FileDir (path,base) -> f path base | FileRegular _ -> () in
  process_directory f path
