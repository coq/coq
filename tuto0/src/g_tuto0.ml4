DECLARE PLUGIN "tuto0"

open Pp
open Ltac_plugin

VERNAC COMMAND EXTEND HelloWorld CLASSIFIED AS QUERY
| [ "HelloWorld" ] -> [ Feedback.msg_notice (strbrk Tuto0_main.message) ]
END

TACTIC EXTEND hello_world_tactic
| [ "hello_world" ] ->
  [ let _ = Feedback.msg_notice (str Tuto0_main.message) in
    Tacticals.New.tclIDTAC ]
END
