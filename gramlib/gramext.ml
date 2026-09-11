(* camlp5r *)
(* gramext.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

type position =
  | First
  | Last
  | Before of string
  | After of string

type g_assoc = NonA | RightA | LeftA | BothA

let pr_assoc = function
  | BothA -> Pp.str "multi associativity"
  | LeftA -> Pp.str "left associativity"
  | RightA -> Pp.str "right associativity"
  | NonA -> Pp.str "no associativity"

(** Returns whether SELF means SELF, respectively on the left and on the right. *)
let split_assoc = function
  | BothA -> (true, true)
  | LeftA -> (true, false)
  | RightA -> (false, true)
  | NonA -> (false, false)

let self_on_the_left assoc = fst (split_assoc assoc)
let self_on_the_right assoc = snd (split_assoc assoc)

let g_assoc_eq a1 a2 =
  match a1, a2 with
  | BothA, BothA -> true
  | LeftA, LeftA -> true
  | RightA, RightA -> true
  | NonA, NonA -> true
  | (BothA | LeftA | RightA | NonA), _ -> false
