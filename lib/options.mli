
(* $Id$ *)

(* Global options of the system. *)

val batch_mode : bool ref

val debug : bool ref

val print_emacs : bool ref
val emacs_str : string -> string

val make_silent : bool -> unit
val is_silent : unit -> bool
val silently : ('a -> 'b) -> 'a -> 'b

