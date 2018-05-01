open Pp

VERNAC COMMAND EXTEND HelloWorld CLASSIFIED AS QUERY
| [ "HelloWorld" ] -> [ Feedback.msg_notice (strbrk "Hello World!") ]
END