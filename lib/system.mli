
(* $Id$ *)

(*s Files. *)

val all_subdirs : string -> string list
val is_in_path : string list -> string -> bool
val where_in_path : string list -> string -> string

val make_suffix : string -> string -> string
val file_readable_p : string -> bool

val glob : string -> string

val home : string

(*s Global load path. *)

val add_path : string -> unit
val del_path : string -> unit
val radd_path : string -> unit

val search_paths : unit -> string list

val find_file_in_path : string -> string

(*s Generic input and output functions, parameterized by a magic number
  and a suffix. The intern functions raise the exception [Bad_magic_number]
  when the check fails, with the full file name. *)

val marshal_out : out_channel -> 'a -> unit
val marshal_in : in_channel -> 'a

exception Bad_magic_number of string

val raw_extern_intern : int -> string -> 
  (string -> string * out_channel) * (string -> string * in_channel)

val extern_intern : int -> string -> (string -> 'a -> unit) * (string -> 'a)

(*s Time stamps. *)

type time

val process_time : unit -> float * float
val get_time : unit -> time
val time_difference : time -> time -> float (* in seconds *)
val fmt_time_difference : time -> time -> Pp.std_ppcmds


