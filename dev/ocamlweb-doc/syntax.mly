%{
open Ast
open Parse
%}

%token <string> META INT IDENT
%token <string> OPER
%token LPAR RPAR BAR COMMA COLON BANG FUN DOT RARROW LET COLONEQ IN IF
%token THEN ELSE EVAL AT FOR PROP SET TYPE WILDCARD FIX
%token COFIX MATCH WITH END AND LBRACE RBRACE STRUCT AS SIMPL PERCENT
%token EOF

%start main
%type <Ast.constr_ast> main

%start constr
%type <Ast.constr_ast> constr

%start simple_constr
%type <Ast.constr_ast> simple_constr

%%

main:
          constr EOF { $1 }
;


paren_constr:
          constr COMMA paren_constr  { Pair($1,$3) }
        | constr                     { $1 }
;

constr:
          binder_constr  { $1 }
        | oper_constr    { close_stack $1 }
;

binder_constr:
          BANG ne_binders DOT constr              { Prod($2, $4) }
        | FUN ne_binders type_cstr RARROW constr  { Lambda($2,mk_cast $5 $3) }
        | LET IDENT binders type_cstr COLONEQ constr IN constr
            { Let($2,mk_lambda $3 (mk_cast $6 $4),$8) }
        | LET LPAR comma_binders RPAR COLONEQ constr IN constr
            { LetCase($3,$6,$8) }
        | IF constr THEN constr ELSE constr       { IfCase($2,$4,$6) }
        | fix_constr                              { $1 }
        | EVAL rfun IN constr                     { Eval($2,$4) }
;

comma_binders:
          ne_comma_binders  { $1 }
        |                   { [] }
;

ne_comma_binders:
          binder COMMA ne_comma_binders  { $1 :: $3 }
        | binder                         { [$1] }
;

rfun:
          SIMPL  { Simpl }
;


/* 2 Conflits shift/reduce */
oper_constr:
          oper_constr oper appl_constr
            { parse_term $3 (parse_oper $2 $1) }
        | oper_constr oper binder_constr
            { parse_term $3 (parse_oper $2 $1) }
        | oper_constr oper  { parse_oper $2 $1 }
        |                   { empty }
        | appl_constr       { parse_term $1 empty }
;

oper:
          OPER {$1}
        | COLON {":"}
;

appl_constr:
          simple_constr ne_appl_args  { Appl($1,$2) }
        | AT global simple_constrs    { ApplExpl($2,$3) }
        | simple_constr               { $1 }
;

appl_arg:
          AT INT COLONEQ simple_constr  { (Some $2,$4) }
        | simple_constr                 { (None,$1) }
;

ne_appl_args:
          appl_arg               { [$1] }
        | appl_arg ne_appl_args  { $1::$2 }
;

simple_constr:
          atomic_constr                           { $1 }
        | match_constr                            { $1 }
        | LPAR paren_constr RPAR                  { $2 }
        | simple_constr PERCENT IDENT { Scope($3,$1) }
;

simple_constrs:
          simple_constr simple_constrs  { $1::$2 }
        |                               { [] }
;

atomic_constr:
          global    { Qualid $1 }
        | PROP      { Prop }
        | SET       { Set }
        | TYPE      { Type }
        | INT       { Int $1 }
        | WILDCARD  { Hole }
        | META      { Meta $1 }
;

global:
          IDENT DOT global  { $1 :: $3 }
        | IDENT             { [$1] }
;

/* Conflit normal */
fix_constr:
          fix_kw fix_decl
            { let (id,_,_,_,_ as fx) = $2 in Fixp($1,[fx],id) }
        | fix_kw fix_decl fix_decls FOR IDENT  { Fixp($1, $2::$3, $5) }
;

fix_kw: FIX {Fix} | COFIX {CoFix}
;

fix_decl:
          IDENT binders type_cstr annot COLONEQ constr  { ($1,$2,$3,$4,$6) }
;

fix_decls:
          AND fix_decl fix_decls  { $2::$3 }
        | AND fix_decl            { [$2] }
;

annot:
          LBRACE STRUCT IDENT RBRACE  { Some $3 }
        |                             { None }
;

match_constr:
          MATCH case_items case_type WITH branches END  { Match($2,$3,$5) }
;

case_items:
          case_item                   { [$1] }
        | case_item COMMA case_items  { $1::$3 }
;

case_item:
          constr pred_pattern { ($1,$2) }
;

case_type:
          RARROW constr  { Some $2 }
        |                { None }
;

pred_pattern:
          AS IDENT COLON constr  { (Some $2, Some $4) }
        | AS IDENT               { (Some $2, None) }
        | COLON constr           { (None, Some $2) }
        |                        { (None,None) }
;

branches:
          BAR branch_list  { $2 }
        | branch_list      { $1 }
        |                  { [] }
;

branch_list:
          patterns RARROW constr                  { [$1, $3] }
        | patterns RARROW constr BAR branch_list  { ($1,$3)::$5 }
;

patterns:
          pattern                 { [$1] }
        | pattern COMMA patterns  { $1::$3 }
;

pattern:
          pattern AS IDENT       { PatAs($1,$3) }
        | pattern COLON constr   { PatType($1,$3) }
        | IDENT simple_patterns  { PatConstr($1,$2) }
        | simple_pattern         { $1 }
;

simple_pattern:
          IDENT              { PatVar $1 }
        | LPAR pattern RPAR  { $2 }
;

simple_patterns:
          simple_pattern                  { [$1] }
        | simple_pattern simple_patterns  { $1::$2 }
;

binder:
          IDENT                 { ($1,Hole) }
        | LPAR IDENT type_cstr RPAR  { ($2,$3) }
;

binders:
          ne_binders  { $1 }
        |             { [] }

ne_binders:
          binder             { [$1] }
        | binder ne_binders  { $1::$2 }
;

type_cstr:
          COLON constr  { $2 }
        |               { Hole }
;
