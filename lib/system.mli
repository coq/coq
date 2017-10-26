(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** {5 Coqtop specific system utilities} *)

(** {6 Directories} *)

type unix_path = string (* path in unix-style, with '/' separator *)

type file_kind =
  | FileDir of unix_path * (* basename of path: *) string
  | FileRegular of string (* basename of file *)

val (//) : unix_path -> string -> unix_path

val exists_dir : unix_path -> bool

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

(** {6 Files and load paths} *)

(** Load path entries remember the original root
    given by the user. For efficiency, we keep the full path (field
    [directory]), the root path and the path relative to the root. *)

val all_subdirs : unix_path:string -> (CUnix.physical_path * string list) list
val is_in_path : CUnix.load_path -> string -> bool
val is_in_system_path : string -> bool
val where_in_path :
  ?warn:bool -> CUnix.load_path -> string -> CUnix.physical_path * string
val where_in_path_rex :
  CUnix.load_path -> Str.regexp -> (CUnix.physical_path * string) list

val find_file_in_path :
  ?warn:bool -> CUnix.load_path -> string -> CUnix.physical_path * string

val trust_file_cache : bool ref
(** [trust_file_cache] indicates whether we trust the underlying
    mapped file-system not to change along the execution of Coq. This
    assumption greatly speds up file search, but it is often
    inconvenient in interactive mode *)

val file_exists_respecting_case : string -> string -> bool

(** {6 I/O functions } *)
(** Generic input and output functions, parameterized by a magic number
  and a suffix. The intern functions raise the exception [Bad_magic_number]
  when the check fails, with the full file name and expected/observed magic
  numbers. *)

type magic_number_error = {filename: string; actual: int; expected: int}
exception Bad_magic_number of magic_number_error

val raw_extern_state : int -> string -> out_channel

val raw_intern_state : int -> string -> in_channel

val extern_state : int -> string -> 'a -> unit

val intern_state : int -> string -> 'a

val with_magic_number_check : ('a -> 'b) -> 'a -> 'b

(** Clones of Marshal.to_channel (with flush) and
    Marshal.from_channel (with nice error message) *)

val marshal_out : out_channel -> 'a -> unit
val marshal_in : string -> in_channel -> 'a

(** Clones of Digest.output and Digest.input (with nice error message) *)

val digest_out : out_channel -> Digest.t -> unit
val digest_in : string -> in_channel -> Digest.t

val marshal_out_segment : string -> out_channel -> 'a -> unit
val marshal_in_segment : string -> in_channel -> 'a * int * Digest.t
val skip_in_segment : string -> in_channel -> int * Digest.t

(** {6 Time stamps.} *)

type time

val get_time : unit -> time
val time_difference : time -> time -> float (** in seconds *)
val fmt_time_difference : time -> time -> Pp.t

val with_time : bool -> ('a -> 'b) -> 'a -> 'b

(** {6 Name of current process.} *)
val process_id : unit -> string
