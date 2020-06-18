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
type 'a events =
  ([> `LspManager of event
   |  `DelegationManager of DelegationManager.event ] as 'a) Lwt.t list

val lsp : unit -> 'a events
val handle_event : event -> 'a events Lwt.t

val init : unit -> unit
