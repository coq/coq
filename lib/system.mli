
(* $Id$ *)

(*s Files and load path. *)

val add_path : string -> unit
val del_path : string -> unit

val extern_intern : int -> string -> (string -> 'a -> unit) * (string -> 'a)

(*s Time stamps. *)

type time_stamp

val get_time_stamp : unit -> time_stamp
val compare_time_stamps : time_stamp -> time_stamp -> int

