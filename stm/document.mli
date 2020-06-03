(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The document manager holds the view that Coq has of the currently open
    documents. It makes it easy for IDEs to handle text edits, navigate
    and get feedback. Note that it does not require IDEs to parse vernacular
    sentences. *)

type document

val create_document : Vernacstate.t -> string -> document
(** [create_document st text] creates a fresh document with initial state
    [st] and content defined by [text]. *)

type position =
  { line : int;
    char : int;
  }

type range =
  { range_start : position;
    range_end : position;
  }

type text_edit = range * string

type proof_data = (Proof.data * position) option

val apply_text_edits : document -> text_edit list -> document
(** [apply_text_edits doc edits] updates the text of [doc] with [edits]. The
    new text is not parsed or executed. *)

val validate_document : document -> document
(** [validate_document doc] reparses the text of [doc] and invalidates the
    states impacted by the diff with the previously validated content. If the
    text of [doc] has not changed since the last call to [validate_document], it
    has no effect. *)

val interpret_to_position : document -> position -> document * proof_data
(** [interpret_to_position doc pos] navigates to the last sentence ending
    before or at [pos] and returns the proofview from the resulting state. *)

val interpret_to_previous : document -> document * proof_data
(** [interpret_to_previous doc] navigates to the previous sentence in [doc]
    and returns the proofview from the resulting state. *)

val interpret_to_next : document -> document * proof_data
(** [interpret_to_next doc] navigates to the next sentence in [doc]
    and returns the proofview from the resulting state. *)

val parsed_ranges : document -> range list
(** parsed_ranges [doc] returns the ranges corresponding to the sentences
    that have been parsed in [doc]. *)

val executed_ranges : document -> range list
(** parsed_ranges [doc] returns the ranges corresponding to the sentences
    that have been executed in [doc]. *)

type severity =
  | Warning
  | Error

type diagnostic = {
  range : range;
  message : string;
  severity : severity;
}

val diagnostics : document -> diagnostic list
(** diagnostics [doc] returns the diagnostics corresponding to the sentences
    that have been executed in [doc]. *)
