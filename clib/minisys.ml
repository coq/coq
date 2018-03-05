(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
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

(* Note: this test is possibly used for Coq module/file names but also for
   OCaml filenames, whose syntax as of today is more restrictive for
   module names (only initial letter then letter, digits, _ or quote),
   but more permissive (though disadvised) for file names  *)

let ok_dirname f =
  not (f = "") && f.[0] != '.' &&
  not (List.mem f !skipped_dirnames) &&
  match Unicode.ident_refutation f with None -> true | _ -> false

(* Check directory can be opened *)

let exists_dir dir =
  (* See BZ#5391 on windows failing on a trailing (back)slash *)
  let rec strip_trailing_slash dir =
    let len = String.length dir in
    if len > 0 && (dir.[len-1] = '/' || dir.[len-1] = '\\')
    then strip_trailing_slash (String.sub dir 0 (len-1)) else dir in
  let dir = if Sys.os_type = "Win32" then strip_trailing_slash dir else dir in
  try Sys.is_directory dir with Sys_error _ -> false

let apply_subdir f path name =
  (* we avoid all files and subdirs starting by '.' (e.g. .svn) *)
  (* as well as skipped files like CVS, ... *)
  let base = try Filename.chop_extension name with Invalid_argument _ -> name in
  if ok_dirname base then
    let path = if path = "." then name else path//name in
    match try (Unix.stat path).Unix.st_kind with Unix.Unix_error _ -> Unix.S_BLK with
    | Unix.S_DIR when name = base -> f (FileDir (path,name))
    | Unix.S_REG -> f (FileRegular name)
    | _ -> ()

let readdir dir = try Sys.readdir dir with any -> [||]

let process_directory f path =
  Array.iter (apply_subdir f path) (readdir path)

let process_subdirectories f path =
  let f = function FileDir (path,base) -> f path base | FileRegular _ -> () in
  process_directory f path
