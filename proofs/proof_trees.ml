
(* $Id$ *)

open Term

type bindOcc = 
  | Dep of identifier
  | NoDep of int
  | Com

type 'a substitution = (bindOcc * 'a) list

type tactic_arg =
  | COMMAND       of Coqast.t
  | CONSTR        of constr
  | IDENTIFIER    of identifier
  | INTEGER       of int
  | CLAUSE        of identifier list
  | BINDINGS      of Coqast.t substitution
  | CBINDINGS     of constr   substitution 
  | QUOTED_STRING of string
  | TACEXP        of Coqast.t
  | REDEXP        of string * Coqast.t list
  | FIXEXP        of identifier * int * Coqast.t
  | COFIXEXP      of identifier * Coqast.t
  | LETPATTERNS   of int list option * (identifier * int list) list
  | INTROPATTERN  of intro_pattern

and intro_pattern =
  | IdPat   of identifier
  | DisjPat of intro_pattern list
  | ConjPat of intro_pattern list
  | ListPat of intro_pattern list  

and tactic_expression = string * tactic_arg list
