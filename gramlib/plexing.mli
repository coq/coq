(* camlp5r *)
(* plexing.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(** Lexing for Camlp5 grammars.

   This module defines the Camlp5 lexer type to be used in extensible
   grammars (see module [Grammar]). It also provides some useful functions
   to create lexers. *)

type pattern = (string * string);
    (* Type for values used by the generated code of the EXTEND
       statement to represent terminals in entry rules.
-      The first string is the constructor name (must start with
       an uppercase character). When it is empty, the second string
       is supposed to be a keyword.
-      The second string is the constructor parameter. Empty if it
       has no parameter (corresponding to the 'wildcard' pattern).
-      The way tokens patterns are interpreted to parse tokens is done
       by the lexer, function [tok_match] below. *)

exception Error of string;
    (** A lexing error exception to be used by lexers. *)

(** Lexer type *)

type lexer 'te =
  { tok_func : lexer_func 'te;
    tok_using : pattern -> unit;
    tok_removing : pattern -> unit;
    tok_match : mutable pattern -> 'te -> string;
    tok_text : pattern -> string;
    tok_comm : mutable option (list Ploc.t) }
   (** The type for lexers compatible with camlp5 grammars. The parameter
       type ['te] is the type of the tokens.
-      The field [tok_func] is the main lexer function. See [lexer_func]
       type below.
-      The field [tok_using] is a function called by the [EXTEND]
       statement to warn the lexer that a rule uses this pattern
       (given as parameter). This allow the lexer 1/ to check that
       the pattern constructor is really among its possible constructors
       2/ to enter the keywords in its tables.
-      The field [tok_removing] is a function possibly called by the
       [DELETE_RULE] statement to warn the lexer that this pattern
       (given as parameter) is no more used in the grammar (the grammar
       system maintains a number of usages of all patterns and calls this
       function when this number falls to zero). If it is a keyword, this
       allow the lexer to remove it in its tables.
-      The field [tok_match] is a function called by the camlp5
       grammar system to ask the lexer how the input tokens have to
       be matched against the patterns. Warning: for efficiency, this
       function has to be written as a function taking patterns as
       parameters and, for each pattern value, returning a function
       matching a token, *not* as a function with two parameters.
-      The field [tok_text] is a function called by the grammar
       system to get the name of the tokens for the error messages,
       in case of syntax error, or for the displaying of the rules
       of an entry.
-      The field [tok_comm] is a mutable place where the lexer can
       put the locations of the comments, if its initial value is not
       [None]. If it is [None], nothing has to be done by the lexer. *)

and lexer_func 'te = Stream.t char -> (Stream.t 'te * location_function)
  (** The type of a lexer function (field [tok_func] of the type
      [glexer]). The character stream is the input stream to be
      lexed. The result is a pair of a token stream and a location
      function (see below) for this tokens stream. *)

and location_function = int -> Ploc.t;
  (** The type of a function giving the location of a token in the
      source from the token number in the stream (starting from zero). *)

value lexer_text : pattern -> string;
   (** A simple [tok_text] function. *)

value default_match : pattern -> (string * string) -> string;
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

value lexer_func_of_parser :
  ((Stream.t char * ref int * ref int) -> ('te * Ploc.t)) -> lexer_func 'te;
   (** A lexer function from a lexer written as a char stream parser
       returning the next token and its location. The two references
       with the char stream contain the current line number and the
       position of the beginning of the current line. *)
value lexer_func_of_ocamllex : (Lexing.lexbuf -> 'te) -> lexer_func 'te;
   (** A lexer function from a lexer created by [ocamllex] *)

(** Function to build a stream and a location function *)

value make_stream_and_location :
  (unit -> ('te * Ploc.t)) -> (Stream.t 'te * location_function);
   (** General function *)

(** Useful functions and values *)

value eval_char : string -> char;
value eval_string : Ploc.t -> string -> string;
   (** Convert a char or a string token, where the backslashes had not
       been interpreted into a real char or string; raise [Failure] if
       bad backslash sequence found; [Plexing.eval_char (Char.escaped c)]
       would return [c] and [Plexing.eval_string (String.escaped s)] would
       return [s] *)

value restore_lexing_info : ref (option (int * int));
value input_file : ref string;
value line_nb : ref (ref int);
value bol_pos : ref (ref int);
   (** Special variables used to reinitialize line numbers and position
       of beginning of line with their correct current values when a parser
       is called several times with the same character stream. Necessary
       for directives (e.g. #load or #use) which interrupt the parsing.
       Without usage of these variables, locations after the directives
       can be wrong. *)

(** The lexing buffer used by streams lexers *)

module Lexbuf :
  sig
    type t = 'a;
    value empty : t;
    value add : char -> t -> t;
    value get : t -> string;
  end
;
