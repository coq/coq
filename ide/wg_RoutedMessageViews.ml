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

let message_views ~route_0 : message_views_router =
  let route_table = Hashtbl.create 17 in
  let () = Hashtbl.add route_table 0 route_0 in
object
  method route i =
    try Hashtbl.find route_table i
    with Not_found ->
      (* at least the message will be printed somewhere*)
      Hashtbl.find route_table 0

  method default_route = route_0

  method register_route i mv = Hashtbl.add route_table i mv

  method delete_route i = Hashtbl.remove route_table i

  method has_selection =
    Hashtbl.fold (fun _ v -> (||) v#has_selection) route_table false

  method get_selected_text =
    Option.default ""
      (Hashtbl.fold (fun _ v acc ->
         if v#has_selection then Some v#get_selected_text else acc)
      route_table None)

end
