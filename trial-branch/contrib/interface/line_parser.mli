val parser_loop :
  (unit -> unit) * (int -> string -> char Stream.t -> string list -> 'a) *
  (char Stream.t -> 'b) * (int -> string -> unit) * (int -> string -> unit) *
  (int -> string -> string -> unit) * (int -> string -> unit) -> in_channel -> 'c
val flush_until_end_of_stream : 'a Stream.t -> unit
