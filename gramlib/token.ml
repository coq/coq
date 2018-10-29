(* camlp5r *)
(* token.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

type pattern = Plexing.pattern

exception Error of string

type location = Ploc.t
type location_function = int -> location
type 'te lexer_func = char Stream.t -> 'te Stream.t * location_function

type 'te glexer =
  'te Plexing.lexer =
    { tok_func : 'te lexer_func;
      tok_using : pattern -> unit;
      tok_removing : pattern -> unit;
      mutable tok_match : pattern -> 'te -> string;
      tok_text : pattern -> string;
      mutable tok_comm : location list option }

let make_loc = Ploc.make_unlined
let dummy_loc = Ploc.dummy

let make_stream_and_location = Plexing.make_stream_and_location
let lexer_func_of_parser = Plexing.lexer_func_of_parser
let lexer_func_of_ocamllex = Plexing.lexer_func_of_ocamllex

let eval_char = Plexing.eval_char
let eval_string = Plexing.eval_string

let lexer_text = Plexing.lexer_text
let default_match = Plexing.default_match

let line_nb = Plexing.line_nb
let bol_pos = Plexing.bol_pos
let restore_lexing_info = Plexing.restore_lexing_info
