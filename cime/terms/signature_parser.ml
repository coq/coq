type token =
    IDENT of (string)
  | INT of (string)
  | COMMA
  | COLON
  | SEMICOLON
  | KW_PREFIX
  | KW_INFIX
  | KW_POSTFIX
  | KW_C
  | KW_AC
  | KW_CONSTANT
  | KW_UNARY
  | KW_BINARY
  | EOF
  | AS
  | ARROW

open Parsing
# 12 "terms/signature_parser.mly"

  open Signatures
  open Signature_syntax

(* Line 8, file terms/signature_parser.ml *)
let yytransl_const = [|
  259 (* COMMA *);
  260 (* COLON *);
  261 (* SEMICOLON *);
  262 (* KW_PREFIX *);
  263 (* KW_INFIX *);
  264 (* KW_POSTFIX *);
  265 (* KW_C *);
  266 (* KW_AC *);
  267 (* KW_CONSTANT *);
  268 (* KW_UNARY *);
  269 (* KW_BINARY *);
    0 (* EOF *);
  270 (* AS *);
  271 (* ARROW *);
    0|]

let yytransl_block = [|
  257 (* IDENT *);
  258 (* INT *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\001\000\002\000\002\000\002\000\003\000\004\000\
\008\000\008\000\009\000\010\000\010\000\011\000\006\000\006\000\
\006\000\006\000\007\000\007\000\007\000\007\000\007\000\007\000\
\005\000\005\000\012\000\012\000\000\000\000\000"

let yylen = "\002\000\
\001\000\001\000\003\000\001\000\001\000\003\000\004\000\006\000\
\001\000\003\000\003\000\000\000\002\000\001\000\001\000\001\000\
\001\000\000\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\003\000\001\000\001\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\027\000\028\000\001\000\029\000\000\000\
\000\000\000\000\004\000\030\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\003\000\015\000\016\000\017\000\000\000\
\026\000\006\000\000\000\024\000\019\000\020\000\021\000\022\000\
\023\000\007\000\000\000\000\000\014\000\008\000\000\000\000\000\
\000\000\000\000\000\000\013\000\010\000\011\000"

let yydgoto = "\003\000\
\007\000\012\000\008\000\013\000\009\000\024\000\034\000\038\000\
\039\000\040\000\041\000\010\000"

let yysindex = "\003\000\
\002\000\006\000\000\000\000\000\000\000\000\000\000\000\004\255\
\017\255\019\255\000\000\000\000\018\255\025\255\002\000\012\255\
\006\255\006\000\012\255\000\000\000\000\000\000\000\000\001\255\
\000\000\000\000\001\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\016\255\030\255\000\000\000\000\029\255\020\255\
\030\255\030\255\030\255\000\000\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\033\000\
\000\000\032\255\000\000\000\000\034\000\000\000\000\000\015\255\
\000\000\000\000\015\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\022\255\000\000\000\000\001\000\000\000\
\022\255\022\255\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\023\000\021\000\000\000\000\000\254\255\022\000\013\000\004\000\
\000\000\007\000\255\255\000\000"

let yytablesize = 264
let yytable = "\014\000\
\009\000\006\000\028\000\001\000\002\000\011\000\004\000\005\000\
\015\000\029\000\030\000\031\000\032\000\033\000\025\000\014\000\
\018\000\021\000\022\000\023\000\016\000\017\000\018\000\018\000\
\018\000\018\000\018\000\018\000\019\000\036\000\037\000\042\000\
\002\000\005\000\043\000\025\000\012\000\020\000\026\000\035\000\
\027\000\046\000\000\000\000\000\000\000\045\000\000\000\044\000\
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
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\004\000\005\000\000\000\009\000\004\000\005\000"

let yycheck = "\002\000\
\000\000\000\000\002\001\001\000\002\000\000\000\001\001\002\001\
\005\001\009\001\010\001\011\001\012\001\013\001\017\000\018\000\
\002\001\006\001\007\001\008\001\004\001\003\001\005\001\009\001\
\010\001\011\001\012\001\013\001\004\001\014\001\001\001\003\001\
\000\000\000\000\015\001\004\001\015\001\015\000\018\000\027\000\
\019\000\043\000\255\255\255\255\255\255\042\000\255\255\041\000\
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
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\001\001\002\001\255\255\005\001\001\001\002\001"

let yynames_const = "\
  COMMA\000\
  COLON\000\
  SEMICOLON\000\
  KW_PREFIX\000\
  KW_INFIX\000\
  KW_POSTFIX\000\
  KW_C\000\
  KW_AC\000\
  KW_CONSTANT\000\
  KW_UNARY\000\
  KW_BINARY\000\
  EOF\000\
  AS\000\
  ARROW\000\
  "

let yynames_block = "\
  IDENT\000\
  INT\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun parser_env ->
    Obj.repr((
# 37 "terms/signature_parser.mly"
                              [] ) : (string list * int * Signatures.symbol_fix * Signature_syntax.symbol_theory) list))
; (fun parser_env ->
    let _1 = (peek_val parser_env 0 : 'decl) in
    Obj.repr((
# 38 "terms/signature_parser.mly"
                              [_1] ) : (string list * int * Signatures.symbol_fix * Signature_syntax.symbol_theory) list))
; (fun parser_env ->
    let _1 = (peek_val parser_env 2 : 'decl) in
    let _3 = (peek_val parser_env 0 : (string list * int * Signatures.symbol_fix * Signature_syntax.symbol_theory) list) in
    Obj.repr((
# 39 "terms/signature_parser.mly"
                              _1::_3 ) : (string list * int * Signatures.symbol_fix * Signature_syntax.symbol_theory) list))
; (fun parser_env ->
    Obj.repr((
# 43 "terms/signature_parser.mly"
                                            [] ) : ((string list * int * Signatures.symbol_fix * Signature_syntax.symbol_theory) * ((string list * string)list)) list ))
; (fun parser_env ->
    let _1 = (peek_val parser_env 0 : 'sorted_decl) in
    Obj.repr((
# 44 "terms/signature_parser.mly"
                                            [_1] ) : ((string list * int * Signatures.symbol_fix * Signature_syntax.symbol_theory) * ((string list * string)list)) list ))
; (fun parser_env ->
    let _1 = (peek_val parser_env 2 : 'sorted_decl) in
    let _3 = (peek_val parser_env 0 : ((string list * int * Signatures.symbol_fix * Signature_syntax.symbol_theory) * ((string list * string)list)) list ) in
    Obj.repr((
# 45 "terms/signature_parser.mly"
                                            _1::_3 ) : ((string list * int * Signatures.symbol_fix * Signature_syntax.symbol_theory) * ((string list * string)list)) list ))
; (fun parser_env ->
    let _1 = (peek_val parser_env 3 : 'op_list) in
    let _3 = (peek_val parser_env 1 : 'fix) in
    let _4 = (peek_val parser_env 0 : 'arity) in
    Obj.repr((
# 51 "terms/signature_parser.mly"
    let t,a = _4
    in
      if _3=Infix & a<>2
      then raise (Syntax_error "Infix symbols must be binary")
      else (_1,a,_3,t)
  ) : 'decl))
; (fun parser_env ->
    let _1 = (peek_val parser_env 5 : 'op_list) in
    let _3 = (peek_val parser_env 3 : 'fix) in
    let _4 = (peek_val parser_env 2 : 'arity) in
    let _6 = (peek_val parser_env 0 : 'profile_list) in
    Obj.repr((
# 61 "terms/signature_parser.mly"
      let t,a = _4 in
        if _3=Infix & a<>2
          then raise (Syntax_error "Infix symbols must be binary")
          else 
	    if (List.exists (fun (x,y) -> (List.length x)<>a) _6)
	    then raise (Syntax_error "Profile must be compatible with arity")  
	    else 
	      ((_1,a,_3,t),_6)
	    ) : 'sorted_decl))
; (fun parser_env ->
    let _1 = (peek_val parser_env 0 : 'profile) in
    Obj.repr((
# 73 "terms/signature_parser.mly"
                                 [_1]   ) : 'profile_list))
; (fun parser_env ->
    let _1 = (peek_val parser_env 2 : 'profile) in
    let _3 = (peek_val parser_env 0 : 'profile_list) in
    Obj.repr((
# 74 "terms/signature_parser.mly"
                                 _1::_3 ) : 'profile_list))
; (fun parser_env ->
    let _1 = (peek_val parser_env 2 : 'sort_list) in
    let _3 = (peek_val parser_env 0 : 'sort) in
    Obj.repr((
# 78 "terms/signature_parser.mly"
                           (_1,_3) ) : 'profile))
; (fun parser_env ->
    Obj.repr((
# 82 "terms/signature_parser.mly"
                          [] ) : 'sort_list))
; (fun parser_env ->
    let _1 = (peek_val parser_env 1 : 'sort) in
    let _2 = (peek_val parser_env 0 : 'sort_list) in
    Obj.repr((
# 83 "terms/signature_parser.mly"
                          _1::_2 ) : 'sort_list))
; (fun parser_env ->
    let _1 = (peek_val parser_env 0 : string) in
    Obj.repr((
# 86 "terms/signature_parser.mly"
                          _1 ) : 'sort))
; (fun parser_env ->
    Obj.repr((
# 90 "terms/signature_parser.mly"
                  Prefix ) : 'fix))
; (fun parser_env ->
    Obj.repr((
# 91 "terms/signature_parser.mly"
                  Infix  ) : 'fix))
; (fun parser_env ->
    Obj.repr((
# 92 "terms/signature_parser.mly"
                  Postfix ) : 'fix))
; (fun parser_env ->
    Obj.repr((
# 93 "terms/signature_parser.mly"
                  Default ) : 'fix))
; (fun parser_env ->
    Obj.repr((
# 96 "terms/signature_parser.mly"
                 (Commutative,2) ) : 'arity))
; (fun parser_env ->
    Obj.repr((
# 97 "terms/signature_parser.mly"
                 (Ac,2) ) : 'arity))
; (fun parser_env ->
    Obj.repr((
# 98 "terms/signature_parser.mly"
                 (Free,0) ) : 'arity))
; (fun parser_env ->
    Obj.repr((
# 99 "terms/signature_parser.mly"
                 (Free,1) ) : 'arity))
; (fun parser_env ->
    Obj.repr((
# 100 "terms/signature_parser.mly"
                 (Free,2) ) : 'arity))
; (fun parser_env ->
    let _1 = (peek_val parser_env 0 : string) in
    Obj.repr((
# 101 "terms/signature_parser.mly"
                 (Free,int_of_string _1) ) : 'arity))
; (fun parser_env ->
    let _1 = (peek_val parser_env 0 : 'ident) in
    Obj.repr((
# 104 "terms/signature_parser.mly"
                         [_1] ) : 'op_list))
; (fun parser_env ->
    let _1 = (peek_val parser_env 2 : 'ident) in
    let _3 = (peek_val parser_env 0 : 'op_list) in
    Obj.repr((
# 105 "terms/signature_parser.mly"
                         _1::_3 ) : 'op_list))
; (fun parser_env ->
    let _1 = (peek_val parser_env 0 : string) in
    Obj.repr((
# 108 "terms/signature_parser.mly"
          _1 ) : 'ident))
; (fun parser_env ->
    let _1 = (peek_val parser_env 0 : string) in
    Obj.repr((
# 109 "terms/signature_parser.mly"
          _1 ) : 'ident))
(* Entry signature *)
; (fun parser_env -> raise (YYexit (peek_val parser_env 0)))
(* Entry sorted_signature *)
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
let signature (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (yyparse yytables 1 lexfun lexbuf : (string list * int * Signatures.symbol_fix * Signature_syntax.symbol_theory) list)
let sorted_signature (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (yyparse yytables 2 lexfun lexbuf : ((string list * int * Signatures.symbol_fix * Signature_syntax.symbol_theory) * ((string list * string)list)) list )
