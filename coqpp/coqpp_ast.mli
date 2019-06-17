(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type loc = {
  loc_start : Lexing.position;
  loc_end : Lexing.position;
}

type code = { code : string; loc : loc; }

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

type symb =
| SymbToken of string * string option
| SymbEntry of string * string option
| SymbSelf
| SymbNext
| SymbList0 of symb * symb option
| SymbList1 of symb * symb option
| SymbOpt of symb
| SymbRules of ((string option * symb) list * code) list
| SymbQuote of string (** Not used by GRAMMAR EXTEND *)

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

type classification =
| ClassifDefault
| ClassifCode of code
| ClassifName of string

type vernac_rule = {
  vernac_atts : (string * string) list option;
  vernac_state : string option;
  vernac_toks : ext_token list;
  vernac_class : code option;
  vernac_depr : bool;
  vernac_body : code;
}

type vernac_ext = {
  vernacext_name : string;
  vernacext_entry : code option;
  vernacext_class : classification;
  vernacext_state : string option;
  vernacext_rules : vernac_rule list;
}

type vernac_argument_ext = {
  vernacargext_name : string;
  vernacargext_printer : code option;
  vernacargext_rules : tactic_rule list;
}

type argument_type =
| ListArgType of argument_type
| OptArgType of argument_type
| PairArgType of argument_type * argument_type
| ExtraArgType of string

type argument_ext = {
  argext_name : string;
  argext_rules : tactic_rule list;
  argext_type : argument_type option;
  argext_interp : code option;
  argext_glob : code option;
  argext_subst : code option;
  argext_rprinter : code option;
  argext_gprinter : code option;
  argext_tprinter : code option;
}

type node =
| Code of code
| Comment of string
| DeclarePlugin of string
| GramExt of grammar_ext
| VernacExt of vernac_ext
| VernacArgumentExt of vernac_argument_ext
| TacticExt of tactic_ext
| ArgumentExt of argument_ext

type t = node list
