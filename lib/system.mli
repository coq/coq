(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** {5 Rocq REPL specific system utilities} *)

(** {6 Directories} *)

type unix_path = string (* path in unix-style, with '/' separator *)

type file_kind =
  | FileDir of unix_path * (* basename of path: *) string
  | FileRegular of string (* basename of file *)

val (//) : unix_path -> string -> unix_path

val exists_dir : unix_path -> bool

(** [mkdir path] ensures that [path] exists as a directory, creating
    the missing suffix if necessary (like Unix' mkdirhier) *)

val mkdir : unix_path -> unit

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

val warn_cannot_open_dir : ?loc:Loc.t -> string -> unit

(** Load path entries remember the original root
    given by the user. For efficiency, we keep the full path (field
    [directory]), the root path and the path relative to the root. *)

val all_subdirs : unix_path:string -> (CUnix.physical_path * string list) list
val is_in_path : CUnix.load_path -> string -> bool
val is_in_system_path : string -> bool
val where_in_path :
  ?warn:bool -> CUnix.load_path -> string -> CUnix.physical_path * string

(** [get_output_path fname] relativizes [fname] with respect to the
    default output directory if [fname] is not absolute *)
val get_output_path : CUnix.physical_path -> CUnix.physical_path

(** [find_file_in_path ?warn loadpath filename] returns the directory
    name and long name of the first physical occurrence [filename] in
    one of the directory of the [loadpath];
    fails with a user error if no such file exists;
    warn if two or more files exist in the loadpath;
    returns instead the directory name of [filename] is [filename] is
    an absolute path *)
val find_file_in_path :
  ?warn:bool -> CUnix.load_path -> string -> CUnix.physical_path * string

(** [all_in_path loadpath filename] returns the list of the directory
    name and full name of all physical occurrences of [filename] in a
    [loadpath] binding physical paths to some arbitrary key *)
val all_in_path :
  (CUnix.physical_path * 'a) list -> string -> ('a * string) list

val trust_file_cache : bool ref
(** [trust_file_cache] indicates whether we trust the underlying
    mapped file-system not to change along the execution of Rocq. This
    assumption greatly speeds up file search, but it is often
    inconvenient in interactive mode *)

val file_exists_respecting_case : string -> string -> bool

(** {6 I/O functions } *)
(** Generic input and output functions, parameterized by a magic number
  and a suffix. The intern functions raise the exception [Bad_magic_number]
  when the check fails, with the full file name and expected/observed magic
  numbers. *)

type magic_number_error = {filename: string; actual: int32; expected: int32}
exception Bad_magic_number of magic_number_error
exception Bad_version_number of magic_number_error

val with_magic_number_check : ?loc:Loc.t -> ('a -> 'b) -> 'a -> 'b

(** big-endian encoding and decoding of int32 (4 btyes) and int64 (8 bytes) *)

val input_int32 : in_channel -> int32

val input_int64 : in_channel -> int64

val output_int32 : out_channel -> int32 -> unit

val output_int64 : out_channel -> int64 -> unit

(** Clones of Marshal.to_channel (with flush) and
    Marshal.from_channel (with nice error message) *)

val marshal_out : out_channel -> 'a -> unit
val marshal_in : string -> in_channel -> 'a

val check_caml_version : caml:string -> file:string -> unit

(** {6 Time stamps.} *)

type time
type duration

val empty_duration : duration

val get_time : unit -> time
val time_difference : time -> time -> float (** in seconds *)

val duration_between : start:time -> stop:time -> duration
val duration_add : duration -> duration -> duration
val duration_real : duration -> float

val fmt_time_difference : time -> time -> Pp.t
val fmt_duration : duration -> Pp.t

type 'a transaction_result = (('a * duration), (Exninfo.iexn * duration)) Result.t
val measure_duration : ('a -> 'b) -> 'a -> 'b transaction_result
val fmt_transaction_result : 'a transaction_result -> Pp.t

(** {6 Instruction count.} *)

type instruction_count = (Int64.t, string) Result.t

val instructions_between : c_start:instruction_count -> c_end:instruction_count -> instruction_count
val instruction_count_add : instruction_count -> instruction_count -> instruction_count

type 'a instructions_result =
  (('a * instruction_count), (Exninfo.iexn * instruction_count)) Result.t

val count_instructions : ('a -> 'b) -> 'a -> 'b instructions_result

val fmt_instructions_result : 'a instructions_result -> Pp.t

(** [get_toplevel_path program] builds a complete path to the
   executable denoted by [program]. This involves:

   - locating the directory: we don't rely on PATH as to make calls to
   /foo/bin/coqtop chose the right /foo/bin/coqproofworker

   - adding the proper suffix: .exe if in windows.

 Note that this function doesn't check that the executable actually
 exists. This is left back to caller, as well as the choice of
 fallback strategy. We could add a fallback strategy here but it is
 better not to as in most cases if this function fails to construct
 the right name you want you execution to fail rather than fall into
 choosing some random binary from the system-wide installation of
 Rocq. *)
val get_toplevel_path : string -> string
