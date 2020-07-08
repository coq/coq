(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Document

(** The document manager holds the view that Coq has of the currently open
    states. It makes it easy for IDEs to handle text edits, navigate
    and get feedback. Note that it does not require IDEs to parse vernacular
    sentences. *)

type state

val init : Vernacstate.t -> document -> state
(** [init st doc] initializes the document manager with initial vernac state
    [st] and document [doc]. *)

type proof_data = (Proof.data * Position.t) option

type progress_hook = state option -> unit Lwt.t

val apply_text_edits : state -> text_edit list -> state

val validate_document : state -> state
(** [validate_document doc] reparses the text of [doc] and invalidates the
    states impacted by the diff with the previously validated content. If the
    text of [doc] has not changed since the last call to [validate_document], it
    has no effect. *)

val interpret_to_position : ?progress_hook:progress_hook -> state -> Position.t -> (state * proof_data * DelegationManager.events) Lwt.t
(** [interpret_to_position doc pos] navigates to the last sentence ending
    before or at [pos] and returns the proofview from the resulting state. *)

val interpret_to_previous : state -> (state * proof_data * DelegationManager.events) Lwt.t
(** [interpret_to_previous doc] navigates to the previous sentence in [doc]
    and returns the proofview from the resulting state. *)

val interpret_to_next : state -> (state * proof_data * DelegationManager.events) Lwt.t
(** [interpret_to_next doc] navigates to the next sentence in [doc]
    and returns the proofview from the resulting state. *)

val interpret_to_end : ?progress_hook:progress_hook -> state -> (state * proof_data * DelegationManager.events) Lwt.t
(** [interpret_to_next doc] navigates to the last sentence in [doc]
    and returns the proofview from the resulting state. *)

val reset : Vernacstate.t -> state -> state
val executed_ranges : state -> Range.t list * Range.t list

(** parsed_ranges [doc] returns the ranges corresponding to the sentences
    that have been executed and remotely execute in [doc]. *)

type severity =
  | Warning
  | Error

type diagnostic = {
  range : Range.t;
  message : string;
  severity : severity;
}

val diagnostics : state -> diagnostic list
(** diagnostics [doc] returns the diagnostics corresponding to the sentences
    that have been executed in [doc]. *)
