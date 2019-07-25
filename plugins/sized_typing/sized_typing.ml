open Declarations
open Global
open Pp

let set_check_sized b =
  set_typing_flags { (typing_flags ()) with check_sized = b }

let set_check_guarded b =
  set_typing_flags { (typing_flags ()) with check_guarded = b }

let print_typing_flags () =
  let flags = typing_flags () in
  Feedback.msg_notice
    (str "check_guarded: " ++ bool flags.check_guarded ++
    fnl () ++ str "check_sized: " ++ bool flags.check_sized)
