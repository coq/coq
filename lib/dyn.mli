
(*i $Id$ i*)

(* Dynamics. Use with extreme care. Not for kids. *)

type t

val create : string -> ('a -> t) * (t -> 'a)
val tag : t -> string
