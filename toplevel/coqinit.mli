
(* $Id$ *)

(* Initialization. *)

val set_debug : unit -> unit

val set_rcfile : string -> unit
val set_rcuser : string -> unit

val no_load_rc : unit -> unit
val load_rcfile : unit -> unit

val add_include : string -> unit
val push_include : string -> unit
val rec_include : string -> unit

val hm2 : string -> string

val init_load_path : unit -> unit
