
(* $Id$ *)

(*s Files and load paths. Load path entries remember the original root
    given by the user. For efficiency, we keep the full path (field
    [directory]), the root path and the path relative to the root. *)

type load_path_entry = {
  directory : string;
  coq_dirpath : string list }

type load_path = load_path_entry list

val all_subdirs : unix_path:string -> string list option -> load_path
val is_in_path : load_path -> string -> bool
val where_in_path : load_path -> string -> load_path_entry * string

val make_suffix : string -> string -> string
val file_readable_p : string -> bool

val glob : string -> string

val home : string

val exists_dir : string -> bool

val find_file_in_path : load_path -> string -> load_path_entry * string

(*s Generic input and output functions, parameterized by a magic number
  and a suffix. The intern functions raise the exception [Bad_magic_number]
  when the check fails, with the full file name. *)

val marshal_out : out_channel -> 'a -> unit
val marshal_in : in_channel -> 'a

exception Bad_magic_number of string

val raw_extern_intern : int -> string -> 
  (string -> string * out_channel) *
  (load_path -> string -> load_path_entry * string * in_channel)

val extern_intern : 
  int -> string -> (string -> 'a -> unit) * (load_path -> string -> 'a)

(*s Time stamps. *)

type time

val process_time : unit -> float * float
val get_time : unit -> time
val time_difference : time -> time -> float (* in seconds *)
val fmt_time_difference : time -> time -> Pp.std_ppcmds


