/************************************************************************/
/*         *   The Coq Proof Assistant / The Coq Development Team       */
/*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       */
/* <O___,, *       (see CREDITS file for the list of authors)           */
/*   \VV/  **************************************************************/
/*    //   *    This file is distributed under the terms of the         */
/*         *     GNU Lesser General Public License Version 2.1          */
/*         *     (see LICENSE file for the text of the license)         */
/************************************************************************/

%{

open Coqpp_ast

let starts s pat =
  let len = String.length s in
  let patlen = String.length pat in
  if patlen <= len && String.sub s 0 patlen = pat then
    Some (String.sub s patlen (len - patlen))
  else None

let ends s pat =
  let len = String.length s in
  let patlen = String.length pat in
  if patlen <= len && String.sub s (len - patlen) patlen = pat then
    Some (String.sub s 0 (len - patlen))
  else None

let between s pat1 pat2 = match starts s pat1 with
| None -> None
| Some s -> ends s pat2  

let without_sep k sep r =
  if sep <> "" then raise Parsing.Parse_error else k r

let parse_user_entry s sep =
  let table = [
    "ne_", "_list", without_sep (fun r -> Ulist1 r);
    "ne_", "_list_sep", (fun sep r -> Ulist1sep (r, sep));
    "", "_list", without_sep (fun r -> Ulist0 r);
    "", "_list_sep", (fun sep r -> Ulist0sep (r, sep));
    "", "_opt", without_sep (fun r -> Uopt r);
  ] in
  let rec parse s sep = function
  | [] ->
    let () = without_sep ignore sep () in
    begin match starts s "tactic" with
    | Some ("0"|"1"|"2"|"3"|"4"|"5" as s) -> Uentryl ("tactic", int_of_string s)
    | Some _ | None -> Uentry s
    end
  | (pat1, pat2, k) :: rem ->
    match between s pat1 pat2 with
    | None -> parse s sep rem
    | Some s ->
      let r = parse s "" table in
      k sep r      
  in
  parse s sep table

%}

%token <Coqpp_ast.code> CODE
%token <string> COMMENT
%token <string> IDENT QUALID
%token <string> STRING
%token <int> INT
%token VERNAC TACTIC GRAMMAR EXTEND END DECLARE PLUGIN DEPRECATED ARGUMENT
%token RAW_PRINTED GLOB_PRINTED
%token COMMAND CLASSIFIED STATE PRINTED TYPED INTERPRETED GLOBALIZED SUBSTITUTED BY AS
%token BANGBRACKET HASHBRACKET LBRACKET RBRACKET PIPE ARROW FUN COMMA EQUAL STAR
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
| declare_plugin { $1 }
| grammar_extend { $1 }
| vernac_extend { $1 }
| tactic_extend { $1 }
| argument_extend { $1 }
;

declare_plugin:
| DECLARE PLUGIN STRING { DeclarePlugin $3 }
;

grammar_extend:
| GRAMMAR EXTEND qualid_or_ident globals gram_entries END
  { GramExt { gramext_name = $3; gramext_globals = $4; gramext_entries = $5 } }
;

argument_extend:
| ARGUMENT EXTEND IDENT
    typed_opt
    printed_opt
    interpreted_opt
    globalized_opt
    substituted_opt
    raw_printed_opt
    glob_printed_opt
    tactic_rules
  END
  { ArgumentExt {
    argext_name = $3;
    argext_rules = $11;
    argext_rprinter = $9;
    argext_gprinter = $10;
    argext_tprinter = $5;
    argext_interp = $6;
    argext_glob = $7;
    argext_subst = $8;
    argext_type = $4;
  } }
| VERNAC ARGUMENT EXTEND IDENT printed_opt tactic_rules END
  { VernacArgumentExt {
    vernacargext_name = $4;
    vernacargext_printer = $5;
    vernacargext_rules = $6;
  } }
;

printed_opt:
| { None }
| PRINTED BY CODE { Some $3 }
;

raw_printed_opt:
| { None }
| RAW_PRINTED BY CODE { Some $3 }
;

glob_printed_opt:
| { None }
| GLOB_PRINTED BY CODE { Some $3 }
;

interpreted_opt:
| { None }
| INTERPRETED BY CODE { Some $3 }
;

globalized_opt:
| { None }
| GLOBALIZED BY CODE { Some $3 }
;

substituted_opt:
| { None }
| SUBSTITUTED BY CODE { Some $3 }
;

typed_opt:
| { None }
| TYPED AS argtype { Some $3 }
;

argtype:
| IDENT { ExtraArgType $1 }
| argtype IDENT {
    match $2 with
    | "list" -> ListArgType $1
    | "option" ->  OptArgType $1
    | _ -> raise Parsing.Parse_error
  }
| LPAREN argtype STAR argtype RPAREN { PairArgType ($2, $4) }
;

vernac_extend:
| VERNAC vernac_entry EXTEND IDENT vernac_classifier vernac_state vernac_rules END
  { VernacExt {
    vernacext_name = $4;
    vernacext_entry = $2;
    vernacext_class = $5;
    vernacext_state = $6;
    vernacext_rules = $7;
  } }
;

vernac_entry:
| COMMAND { None }
| CODE { Some $1 }
;

vernac_classifier:
| { ClassifDefault }
| CLASSIFIED BY CODE { ClassifCode $3 }
| CLASSIFIED AS IDENT { ClassifName $3 }
;

vernac_state:
| { None }
| STATE IDENT { Some $2 }
;

vernac_rules:
| vernac_rule { [$1] }
| vernac_rule vernac_rules { $1 :: $2 }
;

vernac_rule:
| PIPE vernac_attributes_opt rule_state LBRACKET ext_tokens RBRACKET rule_deprecation rule_classifier ARROW CODE
  { {
      vernac_atts = $2;
      vernac_state = $3;
      vernac_toks = $5;
      vernac_depr = $7;
      vernac_class= $8;
      vernac_body = $10;
  } }
;

rule_state:
| { None }
| BANGBRACKET IDENT RBRACKET { Some $2 }
;

vernac_attributes_opt:
| { None }
| HASHBRACKET vernac_attributes RBRACKET { Some $2 }
;

vernac_attributes:
| vernac_attribute { [$1] }
| vernac_attribute SEMICOLON { [$1] }
| vernac_attribute SEMICOLON vernac_attributes { $1 :: $3 }
;

vernac_attribute:
| qualid_or_ident EQUAL qualid_or_ident { ($1, $3) }
| qualid_or_ident { ($1, $1) }
;

rule_deprecation:
| { false }
| DEPRECATED { true }
;

rule_classifier:
| { None }
| FUN CODE { Some $2 }
;

tactic_extend:
| TACTIC EXTEND IDENT tactic_deprecated tactic_level tactic_rules END
  { TacticExt { tacext_name = $3; tacext_deprecated = $4; tacext_level = $5; tacext_rules = $6 } }
;

tactic_deprecated:
| { None }
| DEPRECATED CODE { Some $2 }
;

tactic_level:
| { None }
| LEVEL INT { Some $2 }
;

tactic_rules:
| { [] }
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
| IDENT {
  let e = parse_user_entry $1 "" in
  ExtNonTerminal (e, TokNone) 
  }
| IDENT LPAREN IDENT RPAREN {
  let e = parse_user_entry $1 "" in
  ExtNonTerminal (e, TokName $3)
  }
| IDENT LPAREN IDENT COMMA STRING RPAREN {
  let e = parse_user_entry $1 $5 in
  ExtNonTerminal (e, TokName $3)
}
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
