
(* $Id$ *)

exception BadToken of string

val add_keyword : string -> unit
val is_keyword : string -> bool
val find_keyword : string -> string

val func : char Stream.t -> (string * string) Stream.t * (int -> int * int)

val add_token : Token.pattern -> unit

val tparse : string * string -> (string * string) Stream.t -> string

val token_text : string * string -> string

type frozen_t
val freeze : unit -> frozen_t
val unfreeze : frozen_t -> unit
val init : unit -> unit
