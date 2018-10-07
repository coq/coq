(* camlp5r *)
(* token.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(** Module deprecated since Camlp5 version 5.00. Use now module Plexing.
    Compatibility assumed. *)

type pattern = Plexing.pattern

exception Error of string
    (** Use now [Plexing.Error] *)

type 'te glexer =
  'te Plexing.lexer =
    { tok_func : 'te Plexing.lexer_func;
      tok_using : pattern -> unit;
      tok_removing : pattern -> unit;
      mutable tok_match : pattern -> 'te -> string;
      tok_text : pattern -> string;
      mutable tok_comm : Ploc.t list option }

type 'te lexer_func = char Stream.t -> 'te Stream.t * location_function
and location_function = int -> Ploc.t

val lexer_text : pattern -> string
   (** Use now [Plexing.lexer_text] *)
val default_match : pattern -> string * string -> string
   (** Use now [Plexing.default_match] *)

val lexer_func_of_parser :
  (char Stream.t * int ref * int ref -> 'te * Ploc.t) -> 'te lexer_func
   (** Use now [Plexing.lexer_func_of_parser] *)
val lexer_func_of_ocamllex : (Lexing.lexbuf -> 'te) -> 'te lexer_func
   (** Use now [Plexing.lexer_func_of_ocamllex] *)

val make_stream_and_location :
  (unit -> 'te * Ploc.t) -> 'te Stream.t * location_function
   (** Use now [Plexing.make_stream_and_location] *)

val eval_char : string -> char
   (** Use now [Plexing.eval_char] *)
val eval_string : Ploc.t -> string -> string
   (** Use now [Plexing.eval_string] *)

val restore_lexing_info : (int * int) option ref
   (** Use now [Plexing.restore_lexing_info] *)
val line_nb : int ref ref
   (** Use now [Plexing.line_nb] *)
val bol_pos : int ref ref
   (** Use now [Plexing.bol_pos] *)

(* deprecated since version 4.08 *)

type location = Ploc.t
val make_loc : int * int -> Ploc.t
val dummy_loc : Ploc.t
