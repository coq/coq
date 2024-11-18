(* camlp5r *)
(* plexing.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(** Lexing for Camlp5 grammars.

   This module defines the Camlp5 lexer type to be used in extensible
   grammars (see module [Grammar]). It also provides some useful functions
   to create lexers. *)

type classifier = Keyword of string | Other of string * string option

(** Lexer type *)

module type S = sig
  type keyword_state
  type te
  type 'c pattern
  val tok_pattern_eq : 'a pattern -> 'b pattern -> ('a, 'b) Util.eq option
  val tok_has_payload : 'a pattern -> bool
  val tok_classify : 'a pattern -> classifier

  (** Returning a stream equipped with a location function *)
  val tok_func : ?loc:Loc.t -> (unit,char) Stream.t -> (keyword_state,te) LStream.t

  val tok_match : 'c pattern -> te -> 'c
  val tok_text : 'c pattern -> string

  (* State for the comments, at some point we should make it functional *)
  module State : sig
    type t
    val init : unit -> t
    val set : t -> unit
    val get : unit -> t
    val drop : unit -> unit
    val get_comments : t -> ((int * int) * string) list
  end

end
