
(*i $Id$ i*)

(*i*)
open Pp
(*i*)

(* Error report. *)

val print_loc : Coqast.loc -> std_ppcmds

val explain_exn : exn -> std_ppcmds

val explain_exn_function : (exn -> std_ppcmds) ref
val explain_exn_default : exn -> std_ppcmds

val raise_if_debug : exn -> unit
