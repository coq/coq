(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type loc = {
  loc_start : Lexing.position;
  loc_end : Lexing.position;
}

type code = { code : string }

type user_symbol =
| Ulist1 of user_symbol
| Ulist1sep of user_symbol * string
| Ulist0 of user_symbol
| Ulist0sep of user_symbol * string
| Uopt of user_symbol
| Uentry of string
| Uentryl of string * int

type token_data =
| TokNone
| TokName of string

type ext_token =
| ExtTerminal of string
| ExtNonTerminal of user_symbol * token_data

type tactic_rule = {
  tac_toks : ext_token list;
  tac_body : code;
}

type level = string

type position =
| First
| Last
| Before of level
| After of level
| Level of level

type assoc =
| LeftA
| RightA
| NonA

type gram_symbol =
| GSymbString of string
| GSymbQualid of string * level option
| GSymbParen of gram_symbol list
| GSymbProd of gram_prod list

and gram_prod = {
  gprod_symbs : (string option * gram_symbol list) list;
  gprod_body : code;
}

type gram_rule = {
  grule_label : string option;
  grule_assoc : assoc option;
  grule_prods : gram_prod list;
}

type grammar_entry = {
  gentry_name : string;
  gentry_pos : position option;
  gentry_rules : gram_rule list;
}

type grammar_ext = {
  gramext_name : string;
  gramext_globals : string list;
  gramext_entries : grammar_entry list;
}

type tactic_ext = {
  tacext_name : string;
  tacext_level : int option;
  tacext_deprecated : code option;
  tacext_rules : tactic_rule list;
}

type node =
| Code of code
| Comment of string
| DeclarePlugin of string
| GramExt of grammar_ext
| VernacExt
| TacticExt of tactic_ext

type t = node list
