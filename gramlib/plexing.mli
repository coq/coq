(* camlp5r *)
(* plexing.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(** Lexing for Camlp5 grammars.

   This module defines the Camlp5 lexer type to be used in extensible
   grammars (see module [Grammar]). It also provides some useful functions
   to create lexers. *)

(** Lexer type *)

type 'te lexer_func = ?loc:Loc.t -> char Stream.t -> 'te Stream.t * location_function
and location_function = int -> Loc.t
  (** The type of a function giving the location of a token in the
      source from the token number in the stream (starting from zero). *)

module type Lexer = sig
  type te
  type 'c pattern
  val tok_pattern_eq : 'a pattern -> 'b pattern -> ('a, 'b) Util.eq option
  val tok_pattern_strings : 'c pattern -> string * string option
  val tok_func : te lexer_func
  val tok_using : 'c pattern -> unit
  val tok_removing : 'c pattern -> unit
  val tok_match : 'c pattern -> te -> 'c
  val tok_text : 'c pattern -> string
end
