(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

class command_window : string -> Coq.coqtop -> CoqOps.coqops -> Wg_RoutedMessageViews.message_views_router ->
  object
    method new_query : ?command:string -> ?term:string -> unit -> unit
    method pack_in : (GObj.widget -> unit) -> unit
    method show : unit
    method hide : unit
    method visible : bool
  end
