(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** {5 System utilities} *)

type physical_path = string
type load_path = physical_path list

val physical_path_of_string : string -> physical_path
val string_of_physical_path : physical_path -> string

(** Escape what has to be escaped (e.g. surround with quotes if with spaces) *)
val escaped_string_of_physical_path : physical_path -> string

val canonical_path_name : string -> string

(** Remove all initial "./" in a path *)
val remove_path_dot : string -> string

(** If a path [p] starts with the current directory $PWD then
    [strip_path p] returns the sub-path relative to $PWD.
    Any leading "./" are also removed from the result. *)
val strip_path : string -> string

(** correct_path f dir = dir/f if f is relative *)
val correct_path : string -> string -> string

val path_to_list : string -> string list

(** [make_suffix file suf] catenate [file] with [suf] when
    [file] does not already end with [suf]. *)
val make_suffix : string -> string -> string

(** Return the extension of a file, i.e. its smaller suffix starting
    with "." if any, or "" otherwise. *)
val get_extension : string -> string

val file_readable_p : string -> bool

(** {6 Executing commands } *)

(** [run_command com] launches command [com], and returns
    the contents of stdout and stderr. If given, [~hook]
    is called on each elements read on stdout or stderr. *)

val run_command :
  ?hook:(bytes->unit) -> string -> Unix.process_status * string

(** [sys_command] launches program [prog] with arguments [args].
    It behaves like [Sys.command], except that we rely on
    [Unix.create_process], it's hardly more complex and avoids dealing
    with shells. In particular, no need to quote arguments
    (against whitespace or other funny chars in paths), hence no need
    to care about the different quoting conventions of /bin/sh and cmd.exe. *)

val sys_command : string -> string list -> Unix.process_status

(** A version of [Unix.waitpid] immune to EINTR exceptions *)

val waitpid_non_intr : int -> Unix.process_status

(** Check if two file names refer to the same (existing) file *)
val same_file : string -> string -> bool

