open Pp
(* This one is necessary, to avoid message about missing wit_string *)
open Stdarg

VERNAC COMMAND EXTEND HelloWorld CLASSIFIED AS QUERY
| [ "Hello" string(s) ] ->
  [ Feedback.msg_notice (strbrk "Hello " ++ str s) ]
END

(* reference is allowed as a syntactic entry, but so are all the entries
   found the signature of module Prim in file coq/parsing/pcoq.mli *)

VERNAC COMMAND EXTEND HelloAgain CLASSIFIED AS QUERY
| [ "HelloAgain" reference(r)] ->
(* The function Libnames.pr_reference was found by searching all mli files
   for a function of type reference -> Pp.t *)
  [ Feedback.msg_notice
      (strbrk "Hello again " ++ Libnames.pr_reference r)]
END

(* According to parsing/pcoq.mli, e has type constr_expr *)
(* this type is defined in pretyping/constrexpr.ml *)
(* Question for the developers: why is the file constrexpr.ml and not
   constrexpr.mli --> Easier for packing the software in components. *)
VERNAC COMMAND EXTEND TakingConstr CLASSIFIED AS QUERY
| [ "Cmd1" constr(e) ] ->
  [ let _ = e in Feedback.msg_notice (strbrk "Cmd1 parsed something") ]
END

(* The next step is to make something of parsed expression.
   Interesting information in interp/constrintern.mli *)

(* There are several phases of transforming a parsed expression into
  the final internal data-type (constr).  There exists a collection of
  functions that combine all the phases *)

VERNAC COMMAND EXTEND TakingConstr2 CLASSIFIED AS QUERY
| [ "Cmd2" constr(e) ] ->
  [ let _ = Constrintern.interp_constr
    (Global.env())
    (* Make sure you don't use Evd.empty here, as this does not
      check consistency with existing universe constraints. *)
    (Evd.from_env (Global.env())) e in
    Feedback.msg_notice (strbrk "Cmd2 parsed something legitimate") ]
END

(* This is to show what happens when typing in an empty environment
  with an empty evd.
 Question for the developers: why does "Cmd3 (fun x : nat => x)."
 raise an anomaly, not the same error as "Cmd3 (fun x : a => x)." *)
 
VERNAC COMMAND EXTEND TakingConstr3 CLASSIFIED AS QUERY
| [ "Cmd3" constr(e) ] ->
  [ let _ = Constrintern.interp_constr Environ.empty_env
      Evd.empty e in
      Feedback.msg_notice
        (strbrk "Cmd3 accepted something in the empty context")]
END

(* When adding a definition, we have to be careful that just
  the operation of constructing a well-typed term may already change
  the environment, at the level of universe constraints (which
  are recorded in the evd component).  The fonction
  Constrintern.interp_constr ignores this side-effect, so it should
  not be used here. *)

(* Looking at the interface file interp/constrintern.ml4, I lost
  some time because I did not see that the "constr" type appearing
  there was "EConstr.constr" and not "Constr.constr". *)

VERNAC COMMAND EXTEND Define1 CLASSIFIED AS SIDEFF
| [ "Cmd4" ident(i) constr(e) ] ->
  [ let v = Constrintern.interp_constr (Global.env())
      (Evd.from_env (Global.env())) e in
    Simple_declare.packed_declare_definition i v ]
END

VERNAC COMMAND EXTEND Check1 CLASSIFIED AS QUERY
| [ "Cmd5" constr(e) ] ->
  [ let v = Constrintern.interp_constr (Global.env())
      (Evd.from_env (Global.env())) e in
    let (a, ctx) = v in
    let evd = Evd.from_ctx ctx in
      Feedback.msg_notice
      (Termops.print_constr_env (Global.env()) evd
         (Simple_check.simple_check v)) ]
END