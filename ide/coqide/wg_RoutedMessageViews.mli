(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

class type message_views_router = object
  method route : int -> Wg_MessageView.message_view
  method default_route : Wg_MessageView.message_view

  method select_all : unit -> unit
  method has_selection : bool
  method get_selected_text : string

  method register_route : int -> Wg_MessageView.message_view -> unit
  method delete_route : int -> unit
end

val message_views :
  route_0:Wg_MessageView.message_view -> message_views_router
