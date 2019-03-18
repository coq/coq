(* camlp5r *)
(* plexing.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(** Lexing for Camlp5 grammars.

   This module defines the Camlp5 lexer type to be used in extensible
   grammars (see module [Grammar]). It also provides some useful functions
   to create lexers. *)

type pattern = string * string option
    (* Type for values used by the generated code of the EXTEND
       statement to represent terminals in entry rules.
-      The first string is the constructor name (must start with
       an uppercase character). When it is empty, the second string
       is supposed to be a keyword.
-      The second component is the constructor parameter. None if it
       has no parameter (corresponding to the 'wildcard' pattern).
-      The way tokens patterns are interpreted to parse tokens is done
       by the lexer, function [tok_match] below. *)

(** Lexer type *)

type 'te lexer =
  { tok_func : 'te lexer_func;
    tok_using : pattern -> unit;
    tok_removing : pattern -> unit;
    tok_match : pattern -> 'te -> string;
    tok_text : pattern -> string;
  }
and 'te lexer_func = ?loc:Loc.t -> char Stream.t -> 'te Stream.t * location_function
and location_function = int -> Loc.t
  (** The type of a function giving the location of a token in the
      source from the token number in the stream (starting from zero). *)
