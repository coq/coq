open Pp

(*
 * Inspect an input and print a feedback message explaining what it is
 *)
let print_input (a : 'a) (printer : 'a -> Pp.t) (type_str : string) : unit =
  let msg = printer a ++ strbrk (Printf.sprintf " is a %s." type_str) in
  Feedback.msg_notice msg
