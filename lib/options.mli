
(* $Id$ *)

(* Global options of the system. *)

val batch_mode : bool ref

val debug : bool ref

val print_emacs : bool ref
val emacs_str : string -> string

val make_silent : bool -> unit
val is_silent : unit -> bool
val verbose : unit -> bool
val silently : ('a -> 'b) -> 'a -> 'b

val set_print_hyps_limit : int -> unit
val unset_print_hyps_limit : unit -> unit
val print_hyps_limit : unit -> int option

val make_mes_ambig : bool -> unit
val is_mes_ambig : unit -> bool
val without_mes_ambig : ('a -> 'b) -> 'a -> 'b

val add_unsafe : string -> unit
val is_unsafe : string -> bool

