(* camlp5r *)
(* plexing.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

type pattern = string * string

type location_function = int -> Loc.t
type 'te lexer_func = ?loc:Loc.t -> char Stream.t -> 'te Stream.t * location_function

type 'te lexer =
  { tok_func : 'te lexer_func;
    tok_using : pattern -> unit;
    tok_removing : pattern -> unit;
    tok_match : pattern -> 'te -> string;
    tok_text : pattern -> string;
  }
