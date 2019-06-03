(*
 * Inspect an input and print a feedback message explaining what it is
 *)
val print_input : 'a -> ('a -> Pp.t) -> string -> unit
