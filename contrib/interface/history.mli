type prf_info;;

val start_proof : string -> unit;;
val historical_undo : string -> int -> int list list
val logical_undo : string -> int -> (int * int) list * (int * int) list * int * int
val dump_sequence : out_channel -> string -> unit
val proof_info_as_string : string -> string
val dump_proof_info : out_channel -> string -> unit
val push_command : string -> int -> int -> unit
val get_path_for_rank : string -> int -> int list
val get_nth_open_path : string -> int -> int list
val border_length : string -> int
