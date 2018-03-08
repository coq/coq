(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

class type message_views_router = object
  method route : int -> Wg_MessageView.message_view
  method default_route : Wg_MessageView.message_view

  method has_selection : bool
  method get_selected_text : string

  method register_route : int -> Wg_MessageView.message_view -> unit
  method delete_route : int -> unit
end

val message_views :
  route_0:Wg_MessageView.message_view -> message_views_router
