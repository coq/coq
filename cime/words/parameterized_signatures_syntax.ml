(***************************************************************************

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

(*

  exception raised when a syntax error occurs.

*)

exception Syntax_error of string;;

type expr = Abstract_constraint.expr

type expr_l = expr list

type letter = string * expr_l

type signature_element = string * expr_l * Abstract_constraint.formula

type signature = signature_element list

type simple_word = letter list

type factor = 
  | Simple of simple_word
  | Exp of simple_word * expr
  | Product of string * expr * expr * simple_word

type word = factor list

type constrained_word = word * Abstract_constraint.formula

type rule = word * word * Abstract_constraint.formula

type rules = rule list
