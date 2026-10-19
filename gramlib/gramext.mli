(* camlp5r *)
(* gramext.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

type position =
  | First
  | Last
  | Before of string
  | After of string

type g_assoc = NonA | RightA | LeftA | BothA

val pr_assoc : g_assoc -> Pp.t
(** Prints a [g_assoc] value. *)

val self_on_the_left : g_assoc -> bool
(** Returns whether SELF means SELF on the left. *)

val self_on_the_right : g_assoc -> bool
(** Returns whether SELF means SELF on the right. *)

val g_assoc_eq : g_assoc -> g_assoc -> bool
