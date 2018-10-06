(* camlp5r *)
(* token.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

type pattern = Plexing.pattern;

exception Error of string;

type location = Ploc.t;
type location_function = int -> location;
type lexer_func 'te = Stream.t char -> (Stream.t 'te * location_function);

type glexer 'te = Plexing.lexer 'te ==
  { tok_func : lexer_func 'te;
    tok_using : pattern -> unit;
    tok_removing : pattern -> unit;
    tok_match : mutable pattern -> 'te -> string;
    tok_text : pattern -> string;
    tok_comm : mutable option (list location) }
;

value make_loc = Ploc.make_unlined;
value dummy_loc = Ploc.dummy;

value make_stream_and_location = Plexing.make_stream_and_location;
value lexer_func_of_parser = Plexing.lexer_func_of_parser;
value lexer_func_of_ocamllex = Plexing.lexer_func_of_ocamllex;

value eval_char = Plexing.eval_char;
value eval_string = Plexing.eval_string;

value lexer_text = Plexing.lexer_text;
value default_match = Plexing.default_match;

value line_nb = Plexing.line_nb;
value bol_pos = Plexing.bol_pos;
value restore_lexing_info = Plexing.restore_lexing_info;
