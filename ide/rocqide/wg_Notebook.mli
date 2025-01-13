(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

class ['a] typed_notebook :
  ('a -> GObj.widget option * GObj.widget option * GObj.widget) ->
  ('a -> unit) ->
  Gtk.notebook Gtk.obj ->
object
  inherit GPack.notebook
  method append_term : 'a -> int
  method prepend_term : 'a -> int
  method insert_term : ?pos:int -> 'a -> int
  method set_term : 'a -> unit
  method get_nth_term : int -> 'a
  method pages : 'a list
  method remove_page : int -> unit
  method current_term : 'a
  method goto_term : 'a -> unit
end

val create :
  ('a -> GObj.widget option * GObj.widget option * GObj.widget) ->
  ('a -> unit) ->
  ?enable_popup:bool ->
  ?group_name:string ->
  ?scrollable:bool ->
  ?show_border:bool ->
  ?show_tabs:bool ->
  ?tab_pos:Gtk.Tags.position ->
  ?border_width:int ->
  ?width:int ->
  ?height:int ->
  ?packing:(GObj.widget -> unit) -> ?show:bool -> unit -> 'a typed_notebook
