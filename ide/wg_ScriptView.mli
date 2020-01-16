(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* An undoable view class *)

type source_view = [ Gtk.text_view | `sourceview ] Gtk.obj

class script_view : source_view -> Coq.coqtop ->
object
  inherit GSourceView4.source_view
  method undo : unit -> unit
  method redo : unit -> unit
  method clear_undo : unit -> unit
  method auto_complete : bool
  method set_auto_complete : bool -> unit
  method right_margin_position : int
  method set_right_margin_position : int -> unit
  method show_right_margin : bool
  method set_show_right_margin : bool -> unit
  method comment : unit -> unit
  method uncomment : unit -> unit
  method apply_unicode_binding : unit -> unit
  method recenter_insert : unit
  method proposal : string option
end

val script_view : Coq.coqtop ->
  ?source_buffer:GSourceView4.source_buffer ->
  ?draw_spaces:int list ->
  ?auto_indent:bool ->
  ?highlight_current_line:bool ->
  ?indent_on_tab:bool ->
  ?indent_width:int ->
  ?insert_spaces_instead_of_tabs:bool ->
  ?right_margin_position:int ->
  ?show_line_marks:bool ->
  ?show_line_numbers:bool ->
  ?show_right_margin:bool ->
  ?tab_width:int ->
  ?editable:bool ->
  ?cursor_visible:bool ->
  ?justification:GtkEnums.justification ->
  ?wrap_mode:GtkEnums.wrap_mode ->
  ?accepts_tab:bool ->
  ?border_width:int ->
  ?width:int ->
  ?height:int ->
  ?packing:(GObj.widget -> unit) ->
  ?show:bool -> unit -> script_view
