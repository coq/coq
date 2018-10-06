(* camlp5r *)
(* token.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(** Module deprecated since Camlp5 version 5.00. Use now module Plexing.
    Compatibility assumed. *)

type pattern = Plexing.pattern;

exception Error of string;
    (** Use now [Plexing.Error] *)

type glexer 'te = Plexing.lexer 'te ==
  { tok_func : Plexing.lexer_func 'te;
    tok_using : pattern -> unit;
    tok_removing : pattern -> unit;
    tok_match : mutable pattern -> 'te -> string;
    tok_text : pattern -> string;
    tok_comm : mutable option (list Ploc.t) }
;

type lexer_func 'te = Stream.t char -> (Stream.t 'te * location_function)
and location_function = int -> Ploc.t;

value lexer_text : pattern -> string;
   (** Use now [Plexing.lexer_text] *)
value default_match : pattern -> (string * string) -> string;
   (** Use now [Plexing.default_match] *)

value lexer_func_of_parser :
  ((Stream.t char * ref int * ref int) -> ('te * Ploc.t)) -> lexer_func 'te;
   (** Use now [Plexing.lexer_func_of_parser] *)
value lexer_func_of_ocamllex : (Lexing.lexbuf -> 'te) -> lexer_func 'te;
   (** Use now [Plexing.lexer_func_of_ocamllex] *)

value make_stream_and_location :
  (unit -> ('te * Ploc.t)) -> (Stream.t 'te * location_function);
   (** Use now [Plexing.make_stream_and_location] *)

value eval_char : string -> char;
   (** Use now [Plexing.eval_char] *)
value eval_string : Ploc.t -> string -> string;
   (** Use now [Plexing.eval_string] *)

value restore_lexing_info : ref (option (int * int));
   (** Use now [Plexing.restore_lexing_info] *)
value line_nb : ref (ref int);
   (** Use now [Plexing.line_nb] *)
value bol_pos : ref (ref int);
   (** Use now [Plexing.bol_pos] *)

(* deprecated since version 4.08 *)

type location = Ploc.t;
value make_loc : (int * int) -> Ploc.t;
value dummy_loc : Ploc.t;
