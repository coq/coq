(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** {5 Coqtop specific system utilities} *)

(** {6 Files and load paths} *)

(** Load path entries remember the original root
    given by the user. For efficiency, we keep the full path (field
    [directory]), the root path and the path relative to the root. *)

val exclude_search_in_dirname : string -> unit

val all_subdirs : unix_path:string -> (CUnix.physical_path * string list) list
val is_in_path : CUnix.load_path -> string -> bool
val is_in_system_path : string -> bool
val where_in_path :
  ?warn:bool -> CUnix.load_path -> string -> CUnix.physical_path * string
val where_in_path_rex :
  CUnix.load_path -> Str.regexp -> (CUnix.physical_path * string) list

val exists_dir : string -> bool

val find_file_in_path :
  ?warn:bool -> CUnix.load_path -> string -> CUnix.physical_path * string

(** {6 I/O functions } *)
(** Generic input and output functions, parameterized by a magic number
  and a suffix. The intern functions raise the exception [Bad_magic_number]
  when the check fails, with the full file name. *)

exception Bad_magic_number of string

val raw_extern_intern : int ->
  (string -> string * out_channel) * (string -> in_channel)

val extern_intern : ?warn:bool -> int ->
  (string -> 'a -> unit) * (CUnix.load_path -> string -> 'a)

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
val fmt_time_difference : time -> time -> Pp.std_ppcmds

val with_time : bool -> ('a -> 'b) -> 'a -> 'b

(** {6 Name of current process.} *)
val process_id : unit -> string
