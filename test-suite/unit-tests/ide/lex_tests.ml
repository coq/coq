open Utest

let log_out_ch = open_log_out_ch __FILE__

let lex s =
  let n =
    let last = String.length s - 1 in
    if s.[last] = '.' then Some last else None in
  let stop = ref None in
  let f i _ = assert(!stop = None); stop := Some i in
  begin try Coq_lex.delimit_sentences f s
  with Coq_lex.Unterminated -> () end;
  if n <> !stop then begin
    let p_opt = function None -> "None" | Some i -> "Some " ^ string_of_int i in
    Printf.fprintf log_out_ch "ERROR: %S\nEXPECTED: %s\nGOT: %s\n" s (p_opt n) (p_opt !stop)
  end;
  n = !stop

let i2s i = "test at line: " ^ string_of_int i

let tests = [

  mk_bool_test (i2s __LINE__) "no quotation" @@ lex
  "foo.+1 bar."
  ;
  mk_bool_test (i2s __LINE__) "quotation" @@ lex
  "foo constr:(xxx)."
  ;
  mk_bool_test (i2s __LINE__) "quotation with dot" @@ lex
  "foo constr:(xxx. yyy)."
  ;
  mk_bool_test (i2s __LINE__) "quotation with dot double paren" @@ lex
  "foo constr:((xxx. (foo.+1 ) \")\" yyy))."
  ;
  mk_bool_test (i2s __LINE__) "quotation with dot paren [" @@ lex
  "foo constr:[xxx. (foo.+1 ) \")\" yyy]."
  ;
  mk_bool_test (i2s __LINE__) "quotation with dot double paren [" @@ lex
  "foo constr:[[xxx. (foo.+1 ) \")\" yyy]]."
  ;
  mk_bool_test (i2s __LINE__) "quotation with dot triple paren [" @@ lex
  "foo constr:[[[xxx. (foo.+1 @@ [] ) \"]])\" yyy]]]."
  ;
  mk_bool_test (i2s __LINE__) "quotation nesting {" @@ lex
  "bar:{{ foo {{ hello. }} }}."
  ;

]

let _ = run_tests __FILE__ log_out_ch tests
