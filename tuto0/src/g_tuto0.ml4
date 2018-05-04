DECLARE PLUGIN "tuto0"

open Pp

VERNAC COMMAND EXTEND HelloWorld CLASSIFIED AS QUERY
| [ "HelloWorld" ] -> [ Feedback.msg_notice (strbrk Tuto0_main.message) ]
END