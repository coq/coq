(* Printing *)

let pr x =
  if CDebug.(get_flag misc) then (Format.printf "@[%s@]" x; flush(stdout);)else ()

let prt0 s = () (* print_string s;flush(stdout)*)

let sinfo s = if CDebug.(get_flag misc) then Feedback.msg_debug (Pp.str s)
let info s = if CDebug.(get_flag misc) then Feedback.msg_debug (Pp.str (s ()))
