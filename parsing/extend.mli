(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)

open Pp
open Ast
open Coqast

type nonterm_prod =
  | ProdList0 of nonterm_prod
  | ProdList1 of nonterm_prod
  | ProdOpt of nonterm_prod
  | ProdPrimitive of (string * string)

type prod_item =
  | Term of Token.pattern
  | NonTerm of nonterm_prod * (string * ast_action_type) option

type grammar_rule = {
  gr_name : string; 
  gr_production : prod_item list; 
  gr_action : Ast.act }

type grammar_entry = { 
  ge_name : string;
  ge_type : ast_action_type;
  gl_assoc : Gramext.g_assoc option;
  gl_rules : grammar_rule list }

type grammar_command = { 
  gc_univ : string; 
  gc_entries : grammar_entry list }

type grammar_associativity = Gramext.g_assoc option
type nonterm =
  | NtShort of string
  | NtQual of string * string
type grammar_production =
  | VTerm of string
  | VNonTerm of loc * nonterm * string option
type raw_grammar_rule = string * grammar_production list * grammar_action
type raw_grammar_entry = 
  string * ast_action_type * grammar_associativity * raw_grammar_rule list

val terminal : string -> string * string

val rename_command : string -> string

(*s Pretty-print. *)

(* Dealing with precedences *)

type precedence = int * int * int

type parenRelation = L | E | Any | Prec of precedence

type ppbox =
  | PpHB of int
  | PpHOVB of int
  | PpHVB of int
  | PpVB of int
  | PpTB

(* unparsing objects *)

type 'pat unparsing_hunk = 
  | PH of 'pat * string option * parenRelation
  | RO of string
  | UNP_BOX of ppbox * 'pat unparsing_hunk list
  | UNP_BRK of int * int
  | UNP_TBRK of int * int
  | UNP_TAB
  | UNP_FNL
  | UNP_INFIX of Libnames.extended_global_reference * string * string *
      (parenRelation * parenRelation)

(* Checks if the precedence of the parent printer (None means the
   highest precedence), and the child's one, follow the given
   relation. *)

type tolerability = (string * precedence) * parenRelation

val tolerable_prec : tolerability option -> (string * precedence) -> bool

val ppcmd_of_box : ppbox -> std_ppcmds -> std_ppcmds

type 'pat syntax_entry = {
  syn_id : string;
  syn_prec: precedence;
  syn_astpat : 'pat;
  syn_hunks : 'pat unparsing_hunk list }

type 'pat syntax_command = { 
  sc_univ : string; 
  sc_entries : 'pat syntax_entry list }

type syntax_rule = string * Coqast.t * Coqast.t unparsing_hunk list
type syntax_entry_ast = precedence * syntax_rule list

val interp_grammar_command :
  string -> (string * string -> entry_type) -> 
      raw_grammar_entry list -> grammar_command

val interp_syntax_entry :
  string -> syntax_entry_ast list -> Ast.astpat syntax_command
