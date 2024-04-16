(* Functions that should be used differently depending on the OCaml version *)
val toploop_use_silently : Format.formatter -> string -> bool
val compenv_handle_exit_with_status_0 : (unit -> unit) -> unit
