type token =
    FORMULA of (string)
  | SEMICOLON
  | PIPE
  | IDENT of (string)
  | EOF
  | POWER
  | FP
  | LPAR
  | RPAR
  | ARROW

open Parsing
# 12 "words/parameterized_signatures_parser.mly"

  open Parameterized_signatures
  open Parameterized_signatures_syntax
  
(* Line 8, file words/parameterized_signatures_parser.ml *)
let yytransl_const = [|
  258 (* SEMICOLON *);
  259 (* PIPE *);
    0 (* EOF *);
  261 (* POWER *);
  262 (* FP *);
  263 (* LPAR *);
  264 (* RPAR *);
  265 (* ARROW *);
    0|]

let yytransl_block = [|
  257 (* FORMULA *);
  260 (* IDENT *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\004\000\004\000\004\000\005\000\005\000\002\000\
\008\000\008\000\009\000\009\000\009\000\012\000\012\000\010\000\
\010\000\010\000\010\000\011\000\011\000\013\000\003\000\015\000\
\015\000\015\000\016\000\016\000\006\000\006\000\014\000\007\000\
\000\000\000\000\000\000"

let yylen = "\002\000\
\001\000\002\000\001\000\002\000\003\000\002\000\004\000\002\000\
\001\000\003\000\000\000\002\000\002\000\000\000\002\000\003\000\
\005\000\007\000\005\000\001\000\002\000\002\000\002\000\000\000\
\001\000\003\000\005\000\003\000\000\000\002\000\001\000\001\000\
\002\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\001\000\033\000\000\000\
\000\000\000\000\000\000\000\000\034\000\000\000\000\000\000\000\
\000\000\000\000\035\000\000\000\000\000\000\000\031\000\000\000\
\000\000\002\000\000\000\022\000\000\000\000\000\020\000\008\000\
\000\000\012\000\000\000\013\000\000\000\000\000\000\000\023\000\
\000\000\000\000\030\000\005\000\000\000\000\000\021\000\032\000\
\010\000\015\000\016\000\000\000\026\000\007\000\000\000\000\000\
\000\000\000\000\019\000\017\000\027\000\000\000\018\000"

let yydgoto = "\004\000\
\007\000\013\000\019\000\008\000\009\000\024\000\049\000\014\000\
\020\000\016\000\017\000\036\000\018\000\025\000\021\000\022\000"

let yysindex = "\048\000\
\013\000\036\255\036\255\000\000\002\255\000\000\000\000\016\000\
\022\255\002\255\027\255\026\255\000\000\032\000\031\255\036\255\
\036\255\033\255\000\000\030\255\053\000\052\255\000\000\053\255\
\002\255\000\000\051\255\000\000\002\255\004\255\000\000\000\000\
\056\255\000\000\036\255\000\000\033\255\002\255\036\255\000\000\
\036\255\056\255\000\000\000\000\002\255\054\255\000\000\000\000\
\000\000\000\000\000\000\055\255\000\000\000\000\040\255\002\255\
\056\255\026\255\000\000\000\000\000\000\006\255\000\000"

let yyrindex = "\000\000\
\000\000\019\000\005\000\000\000\029\000\000\000\000\000\000\000\
\060\000\001\000\000\000\000\000\000\000\000\000\061\000\025\000\
\027\000\009\000\000\000\000\000\000\000\062\000\000\000\023\000\
\001\000\000\000\063\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\025\000\000\000\017\000\000\000\035\000\000\000\
\005\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\031\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\000\000\000\000\037\000\000\000\011\000\225\255\000\000\
\002\000\049\000\244\255\000\000\246\255\233\255\024\000\000\000"

let yytablesize = 294
let yytable = "\030\000\
\029\000\031\000\023\000\015\000\024\000\045\000\037\000\010\000\
\020\000\010\000\054\000\046\000\006\000\063\000\051\000\026\000\
\021\000\034\000\011\000\047\000\028\000\055\000\006\000\027\000\
\011\000\061\000\014\000\029\000\029\000\010\000\028\000\032\000\
\060\000\033\000\011\000\043\000\050\000\038\000\039\000\010\000\
\052\000\011\000\012\000\010\000\059\000\062\000\058\000\031\000\
\001\000\002\000\003\000\047\000\040\000\041\000\005\000\042\000\
\048\000\057\000\056\000\003\000\009\000\025\000\004\000\044\000\
\053\000\035\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\029\000\029\000\029\000\029\000\029\000\029\000\
\029\000\029\000\020\000\020\000\020\000\011\000\020\000\020\000\
\005\000\020\000\021\000\021\000\021\000\011\000\021\000\021\000\
\006\000\021\000\011\000\011\000\014\000\014\000\029\000\029\000\
\028\000\011\000\000\000\014\000\011\000\011\000"

let yycheck = "\012\000\
\000\000\012\000\001\001\002\000\000\000\029\000\017\000\004\001\
\000\000\004\001\042\000\008\001\000\000\008\001\038\000\000\000\
\000\000\016\000\000\000\030\000\010\000\045\000\000\000\002\001\
\000\000\057\000\000\000\001\001\000\000\004\001\000\000\000\000\
\056\000\003\001\000\000\025\000\035\000\005\001\009\001\004\001\
\039\000\006\001\007\001\004\001\055\000\058\000\007\001\058\000\
\001\000\002\000\003\000\062\000\000\000\002\001\004\001\003\001\
\001\001\003\001\005\001\000\000\000\000\000\000\000\000\027\000\
\041\000\017\000\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\002\001\003\001\004\001\005\001\006\001\007\001\
\008\001\009\001\002\001\003\001\004\001\009\001\006\001\007\001\
\004\001\009\001\002\001\003\001\004\001\003\001\006\001\007\001\
\002\001\009\001\002\001\003\001\002\001\003\001\002\001\003\001\
\002\001\009\001\255\255\009\001\002\001\003\001"

let yynames_const = "\
  SEMICOLON\000\
  PIPE\000\
  EOF\000\
  POWER\000\
  FP\000\
  LPAR\000\
  RPAR\000\
  ARROW\000\
  "

let yynames_block = "\
  FORMULA\000\
  IDENT\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun parser_env ->
    Obj.repr((
# 40 "words/parameterized_signatures_parser.mly"
         []) : Parameterized_signatures_syntax.signature))
; (fun parser_env ->
    let _1 = (peek_val parser_env 1 : 'signature) in
    Obj.repr((
# 41 "words/parameterized_signatures_parser.mly"
                   _1) : Parameterized_signatures_syntax.signature))
; (fun parser_env ->
    let _1 = (peek_val parser_env 0 : 'elt) in
    Obj.repr((
# 45 "words/parameterized_signatures_parser.mly"
         [_1]) : 'signature))
; (fun parser_env ->
    let _1 = (peek_val parser_env 1 : 'elt) in
    Obj.repr((
# 46 "words/parameterized_signatures_parser.mly"
                   [_1]) : 'signature))
; (fun parser_env ->
    let _1 = (peek_val parser_env 2 : 'elt) in
    let _3 = (peek_val parser_env 0 : 'signature) in
    Obj.repr((
# 47 "words/parameterized_signatures_parser.mly"
                             _1::_3) : 'signature))
; (fun parser_env ->
    let _1 = (peek_val parser_env 1 : string) in
    let _2 = (peek_val parser_env 0 : 'expr_l) in
    Obj.repr((
# 52 "words/parameterized_signatures_parser.mly"
       _1,_2,Abstract_constraint.True) : 'elt))
; (fun parser_env ->
    let _1 = (peek_val parser_env 3 : string) in
    let _2 = (peek_val parser_env 2 : 'expr_l) in
    let _4 = (peek_val parser_env 0 : 'constr) in
    Obj.repr((
# 54 "words/parameterized_signatures_parser.mly"
       _1,_2,_4) : 'elt))
; (fun parser_env ->
    let _1 = (peek_val parser_env 1 : 'cword) in
    Obj.repr((
# 60 "words/parameterized_signatures_parser.mly"
               _1) : Parameterized_signatures_syntax.constrained_word))
; (fun parser_env ->
    let _1 = (peek_val parser_env 0 : 'word) in
    Obj.repr((
# 65 "words/parameterized_signatures_parser.mly"
        (_1,Abstract_constraint.True) ) : 'cword))
; (fun parser_env ->
    let _1 = (peek_val parser_env 2 : 'word) in
    let _3 = (peek_val parser_env 0 : 'constr) in
    Obj.repr((
# 67 "words/parameterized_signatures_parser.mly"
        (_1,_3) ) : 'cword))
; (fun parser_env ->
    Obj.repr((
# 72 "words/parameterized_signatures_parser.mly"
      [] ) : 'word))
; (fun parser_env ->
    let _1 = (peek_val parser_env 1 : 'factor) in
    let _2 = (peek_val parser_env 0 : 'word) in
    Obj.repr((
# 74 "words/parameterized_signatures_parser.mly"
      _1::_2 ) : 'word))
; (fun parser_env ->
    let _1 = (peek_val parser_env 1 : 'simple_word) in
    let _2 = (peek_val parser_env 0 : 'word_no_simple) in
    Obj.repr((
# 76 "words/parameterized_signatures_parser.mly"
      Simple(_1)::_2 ) : 'word))
; (fun parser_env ->
    Obj.repr((
# 81 "words/parameterized_signatures_parser.mly"
      [] ) : 'word_no_simple))
; (fun parser_env ->
    let _1 = (peek_val parser_env 1 : 'factor) in
    let _2 = (peek_val parser_env 0 : 'word) in
    Obj.repr((
# 83 "words/parameterized_signatures_parser.mly"
      _1::_2 ) : 'word_no_simple))
; (fun parser_env ->
    let _1 = (peek_val parser_env 2 : 'letter) in
    let _3 = (peek_val parser_env 0 : 'expr) in
    Obj.repr((
# 88 "words/parameterized_signatures_parser.mly"
        Exp([_1],_3) ) : 'factor))
; (fun parser_env ->
    let _2 = (peek_val parser_env 3 : 'simple_word) in
    let _5 = (peek_val parser_env 0 : 'expr) in
    Obj.repr((
# 90 "words/parameterized_signatures_parser.mly"
        Exp(_2,_5) ) : 'factor))
; (fun parser_env ->
    let _2 = (peek_val parser_env 5 : string) in
    let _3 = (peek_val parser_env 4 : 'expr) in
    let _4 = (peek_val parser_env 3 : 'expr) in
    let _6 = (peek_val parser_env 1 : 'simple_word) in
    Obj.repr((
# 92 "words/parameterized_signatures_parser.mly"
        Product(_2,_3,_4,_6) ) : 'factor))
; (fun parser_env ->
    let _2 = (peek_val parser_env 3 : string) in
    let _3 = (peek_val parser_env 2 : 'expr) in
    let _4 = (peek_val parser_env 1 : 'expr) in
    let _5 = (peek_val parser_env 0 : 'letter) in
    Obj.repr((
# 94 "words/parameterized_signatures_parser.mly"
        Product(_2,_3,_4,[_5]) ) : 'factor))
; (fun parser_env ->
    let _1 = (peek_val parser_env 0 : 'letter) in
    Obj.repr((
# 99 "words/parameterized_signatures_parser.mly"
        [_1] ) : 'simple_word))
; (fun parser_env ->
    let _1 = (peek_val parser_env 1 : 'simple_word) in
    let _2 = (peek_val parser_env 0 : 'letter) in
    Obj.repr((
# 101 "words/parameterized_signatures_parser.mly"
        _1@[_2] ) : 'simple_word))
; (fun parser_env ->
    let _1 = (peek_val parser_env 1 : string) in
    let _2 = (peek_val parser_env 0 : 'expr_l) in
    Obj.repr((
# 106 "words/parameterized_signatures_parser.mly"
        (_1,_2) ) : 'letter))
; (fun parser_env ->
    let _1 = (peek_val parser_env 1 : 'rules) in
    Obj.repr((
# 113 "words/parameterized_signatures_parser.mly"
        _1 ) : Parameterized_signatures_syntax.rules))
; (fun parser_env ->
    Obj.repr((
# 118 "words/parameterized_signatures_parser.mly"
        [] ) : 'rules))
; (fun parser_env ->
    let _1 = (peek_val parser_env 0 : 'rule) in
    Obj.repr((
# 120 "words/parameterized_signatures_parser.mly"
        [_1] ) : 'rules))
; (fun parser_env ->
    let _1 = (peek_val parser_env 2 : 'rule) in
    let _3 = (peek_val parser_env 0 : 'rules) in
    Obj.repr((
# 122 "words/parameterized_signatures_parser.mly"
        _1 :: _3 ) : 'rules))
; (fun parser_env ->
    let _1 = (peek_val parser_env 4 : 'word) in
    let _3 = (peek_val parser_env 2 : 'word) in
    let _5 = (peek_val parser_env 0 : 'constr) in
    Obj.repr((
# 127 "words/parameterized_signatures_parser.mly"
        (_1,_3,_5) ) : 'rule))
; (fun parser_env ->
    let _1 = (peek_val parser_env 2 : 'word) in
    let _3 = (peek_val parser_env 0 : 'word) in
    Obj.repr((
# 129 "words/parameterized_signatures_parser.mly"
        (_1,_3,Abstract_constraint.True) ) : 'rule))
; (fun parser_env ->
    Obj.repr((
# 136 "words/parameterized_signatures_parser.mly"
        [] ) : 'expr_l))
; (fun parser_env ->
    let _1 = (peek_val parser_env 1 : 'expr) in
    let _2 = (peek_val parser_env 0 : 'expr_l) in
    Obj.repr((
# 138 "words/parameterized_signatures_parser.mly"
        _1::_2 ) : 'expr_l))
; (fun parser_env ->
    let _1 = (peek_val parser_env 0 : string) in
    Obj.repr((
# 142 "words/parameterized_signatures_parser.mly"
             Poly_syntax.expr_of_string _1) : 'expr))
; (fun parser_env ->
    let _1 = (peek_val parser_env 0 : string) in
    Obj.repr((
# 146 "words/parameterized_signatures_parser.mly"
             Poly_syntax.constraint_of_string _1) : 'constr))
(* Entry signature_eof *)
; (fun parser_env -> raise (YYexit (peek_val parser_env 0)))
(* Entry cword_eof *)
; (fun parser_env -> raise (YYexit (peek_val parser_env 0)))
(* Entry rules_eof *)
; (fun parser_env -> raise (YYexit (peek_val parser_env 0)))
|]
let yytables =
  { actions=yyact;
    transl_const=yytransl_const;
    transl_block=yytransl_block;
    lhs=yylhs;
    len=yylen;
    defred=yydefred;
    dgoto=yydgoto;
    sindex=yysindex;
    rindex=yyrindex;
    gindex=yygindex;
    tablesize=yytablesize;
    table=yytable;
    check=yycheck;
    error_function=parse_error;
    names_const=yynames_const;
    names_block=yynames_block }
let signature_eof (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (yyparse yytables 1 lexfun lexbuf : Parameterized_signatures_syntax.signature)
let cword_eof (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (yyparse yytables 2 lexfun lexbuf : Parameterized_signatures_syntax.constrained_word)
let rules_eof (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (yyparse yytables 3 lexfun lexbuf : Parameterized_signatures_syntax.rules)
