
(* $Id$ *)

val line_oriented_channel_to_option: string -> in_channel -> int -> char option

val flush_until_end_of_stream : 'a Stream.t -> unit
