/************************************************************************/
/*  v      *   The Coq Proof Assistant  /  The Coq Development Team     */
/* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     */
/*   \VV/  **************************************************************/
/*    //   *      This file is distributed under the terms of the       */
/*         *       GNU Lesser General Public License Version 2.1        */
/************************************************************************/

%{

open Coqpp_ast

%}

%token <Coqpp_ast.code> CODE
%token <string> COMMENT
%token <string> IDENT QUALID
%token <string> STRING
%token VERNAC TACTIC GRAMMAR EXTEND END
%token LBRACKET RBRACKET PIPE ARROW COMMA EQUAL
%token LPAREN RPAREN COLON SEMICOLON
%token GLOBAL FIRST LAST BEFORE AFTER LEVEL LEFTA RIGHTA NONA
%token EOF

%type <Coqpp_ast.t> file
%start file

%%

file:
| nodes EOF
  { $1 }
;

nodes:
|
  { [] }
| node nodes
  { $1 :: $2 }
;

node:
| CODE { Code $1 }
| COMMENT { Comment $1 }
| grammar_extend { $1 }
| vernac_extend { $1 }
| tactic_extend { $1 }
;

grammar_extend:
| GRAMMAR EXTEND qualid_or_ident globals gram_entries END
  { GramExt { gramext_name = $3; gramext_globals = $4; gramext_entries = $5 } }
;

vernac_extend:
| VERNAC EXTEND IDENT END { VernacExt }
;

tactic_extend:
| TACTIC EXTEND IDENT tactic_rules END { TacticExt ($3, $4)  }
;

tactic_rules:
| tactic_rule { [$1] }
| tactic_rule tactic_rules { $1 :: $2 }
;

tactic_rule:
| PIPE LBRACKET ext_tokens RBRACKET ARROW CODE
  { { tac_toks = $3; tac_body = $6 } }
;

ext_tokens:
| { [] }
| ext_token ext_tokens { $1 :: $2 }
;

ext_token:
| STRING { ExtTerminal $1 }
| IDENT { ExtNonTerminal ($1, TokNone) }
| IDENT LPAREN IDENT RPAREN { ExtNonTerminal ($1, TokName $3) }
| IDENT LPAREN IDENT COMMA STRING RPAREN { ExtNonTerminal ($1, TokNameSep ($3, $5)) }
;

qualid_or_ident:
| QUALID { $1 }
| IDENT { $1 }
;

globals:
| { [] }
| GLOBAL COLON idents SEMICOLON { $3 }
;

idents:
| { [] }
| qualid_or_ident idents { $1 :: $2 }
;

gram_entries:
| { [] }
| gram_entry gram_entries { $1 :: $2 }
;

gram_entry:
| qualid_or_ident COLON position_opt LBRACKET levels RBRACKET SEMICOLON
  { { gentry_name = $1; gentry_pos = $3; gentry_rules = $5; } }
;

position_opt:
| { None }
| position { Some $1 }
;

position:
| FIRST { First }
| LAST { Last }
| BEFORE STRING { Before $2 }
| AFTER STRING { After $2 }
| LEVEL STRING { Level $2 }
;

string_opt:
| { None }
| STRING { Some $1 }
;

assoc_opt:
| { None }
| assoc { Some $1 }
;

assoc:
| LEFTA { LeftA }
| RIGHTA { RightA }
| NONA { NonA }
;

levels:
| level { [$1] }
| level PIPE levels { $1 :: $3 }
;

level:
| string_opt assoc_opt LBRACKET rules_opt RBRACKET
  { { grule_label = $1; grule_assoc = $2; grule_prods = $4; } }
;

rules_opt:
| { [] }
| rules { $1 }
;

rules:
| rule { [$1] }
| rule PIPE rules { $1 :: $3 }
;

rule:
| symbols_opt ARROW CODE
  { { gprod_symbs = $1; gprod_body = $3; } }
;

symbols_opt:
| { [] }
| symbols { $1 }
;

symbols:
| symbol { [$1] }
| symbol SEMICOLON symbols { $1 :: $3 }
;

symbol:
| IDENT EQUAL gram_tokens { (Some $1, $3) }
| gram_tokens { (None, $1) }
;

gram_token:
| qualid_or_ident { GSymbQualid ($1, None) }
| qualid_or_ident LEVEL STRING { GSymbQualid ($1, Some $3) }
| LPAREN gram_tokens RPAREN { GSymbParen $2 }
| LBRACKET rules RBRACKET { GSymbProd $2 }
| STRING { GSymbString $1 }
;

gram_tokens:
| gram_token { [$1] }
| gram_token gram_tokens { $1 :: $2 }
;
