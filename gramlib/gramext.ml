(* camlp5r *)
(* gramext.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

type position =
  | First
  | Last
  | Before of string
  | After of string

type g_assoc = NonA | RightA | LeftA

let pr_assoc = function
  | LeftA -> Pp.str "left associativity"
  | RightA -> Pp.str "right associativity"
  | NonA -> Pp.str "no associativity"
