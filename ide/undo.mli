(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* An undoable view class *)

type source_view = [ Gtk.text_view | `sourceview ] Gtk.obj

class undoable_view : source_view ->
object
  inherit GSourceView2.source_view
  method undo : bool
  method redo : bool
  method clear_undo : unit
end

val undoable_view :
           ?source_buffer:GSourceView2.source_buffer ->
           ?draw_spaces:SourceView2Enums.source_draw_spaces_flags list ->
           ?auto_indent:bool ->
           ?highlight_current_line:bool ->
           ?indent_on_tab:bool ->
           ?indent_width:int ->
           ?insert_spaces_instead_of_tabs:bool ->
           ?right_margin_position:int ->
           ?show_line_marks:bool ->
           ?show_line_numbers:bool ->
           ?show_right_margin:bool ->
           ?smart_home_end:SourceView2Enums.source_smart_home_end_type ->
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
           ?show:bool -> unit -> undoable_view
