(* Printing *)

let pr x =
  if !Flags.debug then (Format.printf "@[%s@]" x; flush(stdout);)else ()

let prt0 s = () (* print_string s;flush(stdout)*)

let sinfo s = if !Flags.debug then Feedback.msg_debug (Pp.str s)
let info s = if !Flags.debug then Feedback.msg_debug (Pp.str (s ()))
