%{

type constr_ast =
  Pair of constr_ast * constr_ast
| Prod of binder list * constr_ast
| Lambda of binder list * constr_ast
| Cast of constr_ast * constr_ast
| Let of string * constr_ast * constr_ast
| LetCase of binder list * constr_ast * constr_ast
| IfCase of constr_ast * constr_ast * constr_ast
| Eval of red_fun * constr_ast
| Infix of string * constr_ast * constr_ast
| Prefix of string * constr_ast
| Postfix of string * constr_ast
| Appl of constr_ast * constr_arg list
| ApplExpl of constr_ast * constr_ast list
| Scope of string * constr_ast
| Qualid of string list
| Prop | Set | Type
| Int of string
| Hole
| Meta of string
| Fixp of fix_kind *
      (string * binder list * constr_ast * string option * constr_ast) list *
      string
| Match of case_item list * constr_ast option *
           (pattern list * constr_ast) list 

and redfun = Simpl

and binder = string * constr_ast

and constr_arg = string option * constr_ast

and fix_kind = Fix | CoFix

and case_item = constr_ast * (string option * constr_ast option)

and pattern = 
  PatAs of pattern * string
| PatType of pattern * constr_ast
| PatConstr of string * pattern list
| PatVar of string
%}

%token <string> META
%token <string> INT
%token <string> IDENT
%token <string> INFIX
%token <string> PREFIX
%token <string> POSTFIX
%token LPAR RPAR BAR COMMA COLON BANG FUN DOT RARROW LET COLONEQ IN IF THEN ELSE EVAL AT FOR BQUOTE PROP SET TYPE WILDCARD FIX COFIX MATCH WITH ENDKW AND LBRACE RBRACE STRUCT AS SIMPL

%start constr
%type <constr_ast> constr

%%

paren_constr:
          constr COMMA paren_constr  { Pair($1,$3) }
        | constr                     { $1 }
;

constr:
          binder_constr  { $1 }
        | oper_constr    { $1}
;

binder_constr:
          BANG ne_binders DOT constr                  { Prod($2, $4) }
        | FUN ne_binders type RARROW constr
            { Lambda($2,Cast($5,$3)) }
        | LET IDENT binders type COLONEQ constr IN constr
            { Let($2,$6,Lambda($3,Cast($8,4))) }
        | LET LPAR comma_binders RPAR COLONEQ constr IN constr
            { LetCase($3,$6,$8) }
        | IF constr THEN constr ELSE constr           { IfCase($2,$4,$6) }
        | fix_constr                                  { $1 }
        | EVAL rfun IN constr                         { Eval($2,$4) }
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


oper_constr:
          oper_constr INFIX oper_constr  { Infix($2,$1,$3) }
        | PREFIX oper_constr             { Prefix($1,$2) }
        | oper_constr POSTFIX            { Postfix($2,$1) }
        | appl_constr                    { $1 }
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
        | BQUOTE IDENT COLON paren_constr BQUOTE  { Scope($2,$4) }
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

fix_constr:
          fix_kw fix_decl
            { let (id,_,_,_,_ as fx) = $2 in Fixp($1,[fx],id) }
        | fix_kw fix_decl fix_decls FOR IDENT  { ($1, $2::$3, $5) }
;

fix_kw: FIX {Fix} | COFIX {CoFix}
;

fix_decl:
          IDENT binders type annot COLONEQ constr  { ($1,$2,$3,$4,$6) }
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
          MATCH case_items case_type WITH branches ENDKW  { Match($2,$3,$5) }
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
        | LPAR IDENT type RPAR  { ($2,$3) }
;

binders:
          ne_binders  { $1 }
        |             { [] }

ne_binders:
          binder             { $1 }
        | binder ne_binders  { $1::$2 }
;

type:
          COLON constr  { $2 }
        |               { Hole }
;

