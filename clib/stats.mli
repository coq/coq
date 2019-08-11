val init : unit -> unit
val set_infiles : string list -> unit
val get_stats_enabled : unit -> bool

val print_stats : unit -> unit

(* callbacks for generating statistics *)
val parser_action : string -> int -> unit
val parser_ext : string -> string -> string -> int -> unit

type pid = {
  file : string;
  char : int;
}

val pid_compare : pid -> pid -> int
