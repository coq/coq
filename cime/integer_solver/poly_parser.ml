type token =
    IDENT of (string)
  | PARGAUCHE
  | PARDROITE
  | SEMICOLON
  | COMMA
  | EOF
  | TRUE
  | FALSE
  | AND
  | OR
  | NOT
  | IMPLIES
  | EQUIV
  | EXISTS
  | FORALL
  | PLUS
  | MINUS
  | EXP
  | MULT
  | DIV
  | VERTICALBAR
  | COMP of (string)
  | INT of (Numbers.t)

open Parsing
# 12 "integer_solver/poly_parser.mly"

  open Abstract_constraint;;

(* Line 7, file integer_solver/poly_parser.ml *)
let yytransl_const = [|
  258 (* PARGAUCHE *);
  259 (* PARDROITE *);
  260 (* SEMICOLON *);
  261 (* COMMA *);
    0 (* EOF *);
  262 (* TRUE *);
  263 (* FALSE *);
  264 (* AND *);
  265 (* OR *);
  266 (* NOT *);
  267 (* IMPLIES *);
  268 (* EQUIV *);
  269 (* EXISTS *);
  270 (* FORALL *);
  271 (* PLUS *);
  272 (* MINUS *);
  273 (* EXP *);
  274 (* MULT *);
  275 (* DIV *);
  276 (* VERTICALBAR *);
    0|]

let yytransl_block = [|
  257 (* IDENT *);
  277 (* COMP *);
  278 (* INT *);
    0|]

let yylhs = "\255\255\
\001\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
\003\000\003\000\003\000\003\000\003\000\003\000\003\000\004\000\
\004\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\000\000\000\000"

let yylen = "\002\000\
\002\000\003\000\003\000\002\000\003\000\003\000\004\000\004\000\
\003\000\003\000\005\000\007\000\003\000\001\000\001\000\001\000\
\002\000\001\000\001\000\003\000\003\000\003\000\002\000\003\000\
\003\000\003\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\018\000\000\000\014\000\015\000\000\000\
\000\000\000\000\000\000\019\000\027\000\000\000\000\000\000\000\
\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\
\000\000\000\000\000\000\000\000\000\000\020\000\013\000\017\000\
\000\000\000\000\000\000\000\000\026\000\000\000\000\000\000\000\
\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000"

let yydgoto = "\003\000\
\013\000\014\000\015\000\022\000"

let yysindex = "\022\000\
\053\255\005\255\000\000\000\000\053\255\000\000\000\000\053\255\
\255\254\255\254\005\255\000\000\000\000\097\255\097\000\005\255\
\064\255\090\255\065\255\000\000\255\254\013\255\020\255\249\254\
\005\255\005\255\006\255\005\255\005\255\005\255\005\255\000\000\
\053\255\053\255\053\255\053\255\023\255\000\000\000\000\000\000\
\053\255\053\255\251\254\251\254\000\000\249\254\249\254\064\255\
\104\255\000\000\022\255\078\255\078\255\078\255\078\255\005\255\
\111\255\005\255\064\255"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\033\000\000\000\000\000\000\000\043\255\000\000\000\000\001\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\043\000\057\000\000\000\015\000\029\000\071\000\
\078\000\000\000\104\000\002\000\003\000\004\000\005\000\000\000\
\085\000\000\000\092\000"

let yygindex = "\000\000\
\000\000\006\000\011\000\255\255"

let yytablesize = 372
let yytable = "\021\000\
\023\000\005\000\006\000\007\000\008\000\004\000\016\000\017\000\
\023\000\027\000\018\000\027\000\028\000\029\000\024\000\019\000\
\024\000\041\000\020\000\040\000\011\000\037\000\001\000\002\000\
\042\000\038\000\012\000\045\000\025\000\033\000\043\000\044\000\
\028\000\046\000\047\000\048\000\049\000\025\000\026\000\027\000\
\028\000\029\000\021\000\050\000\051\000\052\000\053\000\016\000\
\000\000\000\000\000\000\054\000\055\000\004\000\005\000\000\000\
\022\000\000\000\006\000\007\000\000\000\057\000\008\000\059\000\
\000\000\009\000\010\000\039\000\011\000\000\000\010\000\000\000\
\033\000\034\000\012\000\035\000\036\000\009\000\025\000\026\000\
\027\000\028\000\029\000\000\000\011\000\033\000\034\000\000\000\
\035\000\036\000\000\000\012\000\038\000\000\000\000\000\000\000\
\032\000\000\000\000\000\000\000\000\000\000\000\000\000\003\000\
\025\000\026\000\027\000\028\000\029\000\030\000\031\000\025\000\
\026\000\027\000\028\000\029\000\030\000\031\000\025\000\026\000\
\027\000\028\000\029\000\000\000\056\000\025\000\026\000\027\000\
\028\000\029\000\000\000\058\000\000\000\000\000\000\000\000\000\
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
\000\000\000\000\000\000\023\000\005\000\006\000\007\000\008\000\
\023\000\023\000\000\000\023\000\023\000\000\000\000\000\023\000\
\023\000\024\000\023\000\023\000\023\000\023\000\024\000\024\000\
\000\000\024\000\024\000\000\000\000\000\024\000\024\000\025\000\
\024\000\024\000\024\000\024\000\025\000\025\000\000\000\025\000\
\025\000\000\000\000\000\025\000\025\000\021\000\025\000\025\000\
\025\000\025\000\021\000\021\000\000\000\021\000\021\000\000\000\
\000\000\021\000\021\000\022\000\000\000\000\000\021\000\021\000\
\022\000\022\000\000\000\022\000\022\000\000\000\000\000\022\000\
\022\000\010\000\000\000\000\000\022\000\022\000\010\000\010\000\
\009\000\010\000\010\000\000\000\000\000\009\000\009\000\011\000\
\009\000\009\000\000\000\000\000\011\000\011\000\012\000\011\000\
\011\000\000\000\000\000\012\000\012\000\000\000\012\000\012\000\
\033\000\034\000\003\000\035\000\036\000\000\000\000\000\000\000\
\003\000\000\000\003\000\003\000"

let yycheck = "\001\001\
\000\000\000\000\000\000\000\000\000\000\001\001\002\001\002\000\
\010\000\017\001\005\000\017\001\018\001\019\001\000\000\005\000\
\011\000\005\001\008\000\021\000\016\001\016\000\001\000\002\000\
\005\001\003\001\022\001\022\001\000\000\008\001\025\000\026\000\
\000\000\028\000\029\000\030\000\031\000\015\001\016\001\017\001\
\018\001\019\001\000\000\033\000\034\000\035\000\036\000\005\001\
\255\255\255\255\255\255\041\000\042\000\001\001\002\001\255\255\
\000\000\255\255\006\001\007\001\255\255\056\000\010\001\058\000\
\255\255\013\001\014\001\003\001\016\001\255\255\000\000\255\255\
\008\001\009\001\022\001\011\001\012\001\000\000\015\001\016\001\
\017\001\018\001\019\001\255\255\000\000\008\001\009\001\255\255\
\011\001\012\001\255\255\000\000\003\001\255\255\255\255\255\255\
\000\000\255\255\255\255\255\255\255\255\255\255\255\255\000\000\
\015\001\016\001\017\001\018\001\019\001\020\001\021\001\015\001\
\016\001\017\001\018\001\019\001\020\001\021\001\015\001\016\001\
\017\001\018\001\019\001\255\255\021\001\015\001\016\001\017\001\
\018\001\019\001\255\255\021\001\255\255\255\255\255\255\255\255\
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
\255\255\255\255\255\255\003\001\003\001\003\001\003\001\003\001\
\008\001\009\001\255\255\011\001\012\001\255\255\255\255\015\001\
\016\001\003\001\018\001\019\001\020\001\021\001\008\001\009\001\
\255\255\011\001\012\001\255\255\255\255\015\001\016\001\003\001\
\018\001\019\001\020\001\021\001\008\001\009\001\255\255\011\001\
\012\001\255\255\255\255\015\001\016\001\003\001\018\001\019\001\
\020\001\021\001\008\001\009\001\255\255\011\001\012\001\255\255\
\255\255\015\001\016\001\003\001\255\255\255\255\020\001\021\001\
\008\001\009\001\255\255\011\001\012\001\255\255\255\255\015\001\
\016\001\003\001\255\255\255\255\020\001\021\001\008\001\009\001\
\003\001\011\001\012\001\255\255\255\255\008\001\009\001\003\001\
\011\001\012\001\255\255\255\255\008\001\009\001\003\001\011\001\
\012\001\255\255\255\255\008\001\009\001\255\255\011\001\012\001\
\008\001\009\001\003\001\011\001\012\001\255\255\255\255\255\255\
\009\001\255\255\011\001\012\001"

let yynames_const = "\
  PARGAUCHE\000\
  PARDROITE\000\
  SEMICOLON\000\
  COMMA\000\
  EOF\000\
  TRUE\000\
  FALSE\000\
  AND\000\
  OR\000\
  NOT\000\
  IMPLIES\000\
  EQUIV\000\
  EXISTS\000\
  FORALL\000\
  PLUS\000\
  MINUS\000\
  EXP\000\
  MULT\000\
  DIV\000\
  VERTICALBAR\000\
  "

let yynames_block = "\
  IDENT\000\
  COMP\000\
  INT\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun parser_env ->
    let _1 = (peek_val parser_env 1 : 'formula) in
    Obj.repr((
# 45 "integer_solver/poly_parser.mly"
                _1 ) : Abstract_constraint.formula))
; (fun parser_env ->
    let _1 = (peek_val parser_env 2 : 'formula) in
    let _3 = (peek_val parser_env 0 : 'formula) in
    Obj.repr((
# 50 "integer_solver/poly_parser.mly"
      conj _1 _3 ) : 'formula))
; (fun parser_env ->
    let _1 = (peek_val parser_env 2 : 'formula) in
    let _3 = (peek_val parser_env 0 : 'formula) in
    Obj.repr((
# 52 "integer_solver/poly_parser.mly"
      disj _1 _3 ) : 'formula))
; (fun parser_env ->
    let _2 = (peek_val parser_env 0 : 'formula) in
    Obj.repr((
# 54 "integer_solver/poly_parser.mly"
      Neg(_2) ) : 'formula))
; (fun parser_env ->
    let _1 = (peek_val parser_env 2 : 'formula) in
    let _3 = (peek_val parser_env 0 : 'formula) in
    Obj.repr((
# 56 "integer_solver/poly_parser.mly"
      Implies(_1,_3) ) : 'formula))
; (fun parser_env ->
    let _1 = (peek_val parser_env 2 : 'formula) in
    let _3 = (peek_val parser_env 0 : 'formula) in
    Obj.repr((
# 58 "integer_solver/poly_parser.mly"
      Equiv(_1,_3) ) : 'formula))
; (fun parser_env ->
    let _2 = (peek_val parser_env 2 : 'id_list) in
    let _4 = (peek_val parser_env 0 : 'formula) in
    Obj.repr((
# 60 "integer_solver/poly_parser.mly"
      Exists(_2,_4) ) : 'formula))
; (fun parser_env ->
    let _2 = (peek_val parser_env 2 : 'id_list) in
    let _4 = (peek_val parser_env 0 : 'formula) in
    Obj.repr((
# 62 "integer_solver/poly_parser.mly"
      Forall(_2,_4) ) : 'formula))
; (fun parser_env ->
    let _1 = (peek_val parser_env 2 : Abstract_constraint.expr) in
    let _2 = (peek_val parser_env 1 : string) in
    let _3 = (peek_val parser_env 0 : Abstract_constraint.expr) in
    Obj.repr((
# 64 "integer_solver/poly_parser.mly"
      Comp(_1,_2,_3) ) : 'formula))
; (fun parser_env ->
    let _1 = (peek_val parser_env 2 : Abstract_constraint.expr) in
    let _3 = (peek_val parser_env 0 : Abstract_constraint.expr) in
    Obj.repr((
# 66 "integer_solver/poly_parser.mly"
      Comp(_1,"|",_3) ) : 'formula))
; (fun parser_env ->
    let _1 = (peek_val parser_env 4 : Abstract_constraint.expr) in
    let _2 = (peek_val parser_env 3 : string) in
    let _3 = (peek_val parser_env 2 : Abstract_constraint.expr) in
    let _4 = (peek_val parser_env 1 : string) in
    let _5 = (peek_val parser_env 0 : Abstract_constraint.expr) in
    Obj.repr((
# 68 "integer_solver/poly_parser.mly"
      conj (Comp(_1,_2,_3)) (Comp(_3,_4,_5)) ) : 'formula))
; (fun parser_env ->
    let _1 = (peek_val parser_env 6 : Abstract_constraint.expr) in
    let _2 = (peek_val parser_env 5 : string) in
    let _3 = (peek_val parser_env 4 : Abstract_constraint.expr) in
    let _4 = (peek_val parser_env 3 : string) in
    let _5 = (peek_val parser_env 2 : Abstract_constraint.expr) in
    let _6 = (peek_val parser_env 1 : string) in
    let _7 = (peek_val parser_env 0 : Abstract_constraint.expr) in
    Obj.repr((
# 70 "integer_solver/poly_parser.mly"
      conj (conj (Comp(_1,_2,_3)) (Comp(_3,_4,_5))) (Comp(_5,_6,_7)) ) : 'formula))
; (fun parser_env ->
    let _2 = (peek_val parser_env 1 : 'formula) in
    Obj.repr((
# 72 "integer_solver/poly_parser.mly"
      _2 ) : 'formula))
; (fun parser_env ->
    Obj.repr((
# 74 "integer_solver/poly_parser.mly"
      True ) : 'formula))
; (fun parser_env ->
    Obj.repr((
# 76 "integer_solver/poly_parser.mly"
      False ) : 'formula))
; (fun parser_env ->
    let _1 = (peek_val parser_env 0 : string) in
    Obj.repr((
# 81 "integer_solver/poly_parser.mly"
      [_1] ) : 'id_list))
; (fun parser_env ->
    let _1 = (peek_val parser_env 1 : string) in
    let _2 = (peek_val parser_env 0 : 'id_list) in
    Obj.repr((
# 83 "integer_solver/poly_parser.mly"
      _1::_2 ) : 'id_list))
; (fun parser_env ->
    let _1 = (peek_val parser_env 0 : string) in
    Obj.repr((
# 88 "integer_solver/poly_parser.mly"
      Var(_1) ) : Abstract_constraint.expr))
; (fun parser_env ->
    let _1 = (peek_val parser_env 0 : Numbers.t) in
    Obj.repr((
# 90 "integer_solver/poly_parser.mly"
      Cte(_1) ) : Abstract_constraint.expr))
; (fun parser_env ->
    let _2 = (peek_val parser_env 1 : Abstract_constraint.expr) in
    Obj.repr((
# 92 "integer_solver/poly_parser.mly"
      _2 ) : Abstract_constraint.expr))
; (fun parser_env ->
    let _1 = (peek_val parser_env 2 : Abstract_constraint.expr) in
    let _3 = (peek_val parser_env 0 : Abstract_constraint.expr) in
    Obj.repr((
# 94 "integer_solver/poly_parser.mly"
      Plus(_1,_3) ) : Abstract_constraint.expr))
; (fun parser_env ->
    let _1 = (peek_val parser_env 2 : Abstract_constraint.expr) in
    let _3 = (peek_val parser_env 0 : Abstract_constraint.expr) in
    Obj.repr((
# 96 "integer_solver/poly_parser.mly"
      Sub(_1,_3) ) : Abstract_constraint.expr))
; (fun parser_env ->
    let _2 = (peek_val parser_env 0 : Abstract_constraint.expr) in
    Obj.repr((
# 98 "integer_solver/poly_parser.mly"
      Minus(_2) ) : Abstract_constraint.expr))
; (fun parser_env ->
    let _1 = (peek_val parser_env 2 : Abstract_constraint.expr) in
    let _3 = (peek_val parser_env 0 : Abstract_constraint.expr) in
    Obj.repr((
# 100 "integer_solver/poly_parser.mly"
      Mult(_1,_3) ) : Abstract_constraint.expr))
; (fun parser_env ->
    let _1 = (peek_val parser_env 2 : Abstract_constraint.expr) in
    let _3 = (peek_val parser_env 0 : Abstract_constraint.expr) in
    Obj.repr((
# 102 "integer_solver/poly_parser.mly"
      Quotient(_1,_3) ) : Abstract_constraint.expr))
; (fun parser_env ->
    let _1 = (peek_val parser_env 2 : Abstract_constraint.expr) in
    let _3 = (peek_val parser_env 0 : Numbers.t) in
    Obj.repr((
# 104 "integer_solver/poly_parser.mly"
      try
	power _1 (Numbers.to_int _3) 
      with 
	Invalid_argument("Numbers.to_int") ->
	  failwith "Exponent too large"
    ) : Abstract_constraint.expr))
(* Entry constraint_entry *)
; (fun parser_env -> raise (YYexit (peek_val parser_env 0)))
(* Entry expr *)
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
let constraint_entry (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (yyparse yytables 1 lexfun lexbuf : Abstract_constraint.formula)
let expr (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (yyparse yytables 2 lexfun lexbuf : Abstract_constraint.expr)
