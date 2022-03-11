(* camlp5r *)
(* gramext.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

type position =
  | First
  | Last
  | Before of string
  | After of string

type g_assoc = NonA | RightA | LeftA

val pr_assoc : g_assoc -> Pp.t
(** Prints a [g_assoc] value. *)
