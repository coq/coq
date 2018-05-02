open Pp
(* This one is necessary, to avoid message about missing wit_string *)
open Stdarg

VERNAC COMMAND EXTEND HelloWorld CLASSIFIED AS QUERY
| [ "Hello" string(s)] ->
  [ Feedback.msg_notice (strbrk "Hello " ++ str s) ]
END

(* reference is allowed as a syntactic entry, but so are all the entries
   found the signature of module Prim in file coq/parsing/pcoq.mli *)

VERNAC COMMAND EXTEND HelloAgain CLASSIFIED AS QUERY
| [ "HelloAgain" reference(r)] ->
(* The function Libnames.pr_reference was found by searchin all mli files
   for a function of type reference -> Pp.t *)
  [ Feedback.msg_notice
      (strbrk "Hello again " ++ Libnames.pr_reference r)]
END

VERNAC COMMAND EXTEND TakingConstr CLASSIFIED AS QUERY
| [ "Cmd1" constr(e) ] ->
  [ Feedback.msg_notice (strbrk "Cmd1 parsed something") ]
END
