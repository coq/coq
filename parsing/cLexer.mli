(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This should be functional but it is not due to the interface *)
val add_keyword : string -> unit
val remove_keyword : string -> unit
val is_keyword : string -> bool
val keywords : unit -> CString.Set.t

type keyword_state
val set_keyword_state : keyword_state -> unit
val get_keyword_state : unit -> keyword_state

val check_ident : string -> unit
val is_ident : string -> bool
val check_keyword : string -> unit
val terminal : string -> Tok.t

(** The lexer of Coq: *)

(* modtype Grammar.GLexerType: sig
     type te val
     lexer : te Plexing.lexer
   end

where

  type lexer 'te =
    { tok_func : lexer_func 'te;
      tok_using : pattern -> unit;
      tok_removing : pattern -> unit;
      tok_match : pattern -> 'te -> string;
      tok_text : pattern -> string;
      tok_comm : mutable option (list location) }
 *)
include Grammar.GLexerType with type te = Tok.t

module Error : sig
  type t
  exception E of t
  val to_string : t -> string
end

(* Mainly for comments state, etc... *)
type lexer_state

val init_lexer_state : Loc.source -> lexer_state
val set_lexer_state : lexer_state -> unit
val get_lexer_state : unit -> lexer_state
val release_lexer_state : unit -> lexer_state
[@@ocaml.deprecated "Use get_lexer_state"]
val drop_lexer_state : unit -> unit
val get_comment_state : lexer_state -> ((int * int) * string) list
