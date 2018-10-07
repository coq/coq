(* camlp5r *)
(* plexing.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(** Lexing for Camlp5 grammars.

   This module defines the Camlp5 lexer type to be used in extensible
   grammars (see module [Grammar]). It also provides some useful functions
   to create lexers. *)

type pattern = string * string
    (* Type for values used by the generated code of the EXTEND
       statement to represent terminals in entry rules.
-      The first string is the constructor name (must start with
       an uppercase character). When it is empty, the second string
       is supposed to be a keyword.
-      The second string is the constructor parameter. Empty if it
       has no parameter (corresponding to the 'wildcard' pattern).
-      The way tokens patterns are interpreted to parse tokens is done
       by the lexer, function [tok_match] below. *)

exception Error of string
    (** A lexing error exception to be used by lexers. *)

(** Lexer type *)

type 'te lexer =
  { tok_func : 'te lexer_func;
    tok_using : pattern -> unit;
    tok_removing : pattern -> unit;
    mutable tok_match : pattern -> 'te -> string;
    tok_text : pattern -> string;
    mutable tok_comm : Ploc.t list option }
and 'te lexer_func = char Stream.t -> 'te Stream.t * location_function
and location_function = int -> Ploc.t
  (** The type of a function giving the location of a token in the
      source from the token number in the stream (starting from zero). *)

val lexer_text : pattern -> string
   (** A simple [tok_text] function. *)

val default_match : pattern -> string * string -> string
   (** A simple [tok_match] function, appling to the token type
       [(string * string)] *)

(** Lexers from parsers or ocamllex

   The functions below create lexer functions either from a [char stream]
   parser or for an [ocamllex] function. With the returned function [f],
   it is possible to get a simple lexer (of the type [Plexing.glexer] above):
   {[
          { Plexing.tok_func = f;
            Plexing.tok_using = (fun _ -> ());
            Plexing.tok_removing = (fun _ -> ());
            Plexing.tok_match = Plexing.default_match;
            Plexing.tok_text = Plexing.lexer_text;
            Plexing.tok_comm = None }
   ]}
   Note that a better [tok_using] function should check the used tokens
   and raise [Plexing.Error] for incorrect ones. The other functions
   [tok_removing], [tok_match] and [tok_text] may have other implementations
   as well. *)

val lexer_func_of_parser :
  (char Stream.t * int ref * int ref -> 'te * Ploc.t) -> 'te lexer_func
   (** A lexer function from a lexer written as a char stream parser
       returning the next token and its location. The two references
       with the char stream contain the current line number and the
       position of the beginning of the current line. *)
val lexer_func_of_ocamllex : (Lexing.lexbuf -> 'te) -> 'te lexer_func
   (** A lexer function from a lexer created by [ocamllex] *)

(** Function to build a stream and a location function *)

val make_stream_and_location :
  (unit -> 'te * Ploc.t) -> 'te Stream.t * location_function
   (** General function *)

(** Useful functions and values *)

val eval_char : string -> char
val eval_string : Ploc.t -> string -> string
   (** Convert a char or a string token, where the backslashes had not
       been interpreted into a real char or string; raise [Failure] if
       bad backslash sequence found; [Plexing.eval_char (Char.escaped c)]
       would return [c] and [Plexing.eval_string (String.escaped s)] would
       return [s] *)

val restore_lexing_info : (int * int) option ref
val input_file : string ref
val line_nb : int ref ref
val bol_pos : int ref ref
   (** Special variables used to reinitialize line numbers and position
       of beginning of line with their correct current values when a parser
       is called several times with the same character stream. Necessary
       for directives (e.g. #load or #use) which interrupt the parsing.
       Without usage of these variables, locations after the directives
       can be wrong. *)

(** The lexing buffer used by streams lexers *)

module Lexbuf :
  sig
    type t
    val empty : t
    val add : char -> t -> t
    val get : t -> string
  end
