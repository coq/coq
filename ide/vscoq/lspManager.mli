(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
type event
type events = event Lwt.t list

val lsp : unit -> events
val handle_event : event -> events Lwt.t
val pr_event : event -> Pp.t
val handle_feedback : Feedback.feedback -> unit

val init : unit -> unit
