(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Scheduler

(** This file defines operations on the content of a document (text, parsing
    of sentences, scheduling). *)

type document

val create_document : string -> document
(** [create_document text] creates a fresh document with content defined by
    [text]. *)

module Position : sig

type t =
  { line : int;
    char : int
  }

val compare : t -> t -> int

end

module Range : sig

type t =
  { start : Position.t;
    stop : Position.t;
  }

end

type text_edit = Range.t * string

val apply_text_edits : document -> text_edit list -> document
(** [apply_text_edits doc edits] updates the text of [doc] with [edits]. The
    new text is not parsed or executed. *)

val parsed_ranges : document -> Range.t list
(** parsed_ranges [doc] returns the ranges corresponding to the sentences
    that have been parsed in [doc]. *)

val validate_document : document -> Stateid.Set.t * document

type parsed_ast =
  | ValidAst of ast * Tok.t list
  | ParseError of string Loc.located

type sentence = {
  start : int;
  stop : int;
  parsing_state : Vernacstate.Parser.t; (* st used to parse this sentence *)
  scheduler_state_before : Scheduler.state;
  scheduler_state_after : Scheduler.state;
  ast : parsed_ast;
  id : sentence_id;
}

(* TODO refine this API *)
val find_sentence : document -> int -> sentence option
val find_sentence_before : document -> int -> sentence option
val more_to_parse : document -> bool
val parsed_loc : document -> int
val schedule : document -> schedule

val position_of_loc : document -> int -> Position.t
val loc_of_position : document -> Position.t -> int

val end_loc : document -> int

val range_of_id : document -> Stateid.t -> Range.t
val range_of_loc : document -> Loc.t -> Range.t
val parse_errors : document -> (Stateid.t * Loc.t option * string) list
val sentences_before : document -> int -> sentence list
