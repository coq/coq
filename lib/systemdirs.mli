(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

type unix_path = string (* path in unix-style, with '/' separator *)

type file_kind =
  | FileDir of unix_path * (* basename of path: *) string 
  | FileRegular of string (* basename of file *)

val (//) : unix_path -> string -> unix_path

val exists_dir : unix_path -> bool

(** [check_unix_dir warn path] calls [warn] with an appropriate
     message if [path] looks does not look like a Unix path on Windows *)

val check_unix_dir : (string -> unit) -> unix_path -> unit

(** [exclude_search_in_dirname path] excludes [path] when processing
    directories *)

val exclude_directory : unix_path -> unit

(** [process_directory f path] applies [f] on contents of directory
    [path]; fails with Unix_error if the latter does not exists; skips
    all files or dirs starting with "." *)

val process_directory : (file_kind -> unit) -> unix_path -> unit

(** [process_subdirectories f path] applies [f path/file file] on each
    [file] of the directory [path]; fails with Unix_error if the
    latter does not exists; kips all files or dirs starting with "." *)

val process_subdirectories : (unix_path -> string -> unit) -> unix_path -> unit
