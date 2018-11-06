(* camlp5r *)
(* plexing.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

type pattern = string * string

exception Error of string

type location = Ploc.t
type location_function = int -> location
type 'te lexer_func = char Stream.t -> 'te Stream.t * location_function

type 'te lexer =
  { tok_func : 'te lexer_func;
    tok_using : pattern -> unit;
    tok_removing : pattern -> unit;
    mutable tok_match : pattern -> 'te -> string;
    tok_text : pattern -> string;
    mutable tok_comm : location list option }
