
(* $Id$ *)

type loc = int * int

type t =
  | Node of loc * string * t list
  | Nvar of loc * string
  | Slam of loc * string option * t
  | Num of loc * int
  | Id of loc * string
  | Str of loc * string
  | Path of loc * string list* string
  | Dynamic of loc * Dyn.t

val hcons_ast: (string -> string) -> (t -> t) * (loc -> loc)

