(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* An undoable view class *)

type source_view = [ Gtk.text_view | `sourceview ] Gtk.obj

class script_view : source_view -> RocqDriver.rocqtop ->
object
  inherit GSourceView3.source_view
  method undo : unit -> unit
  method redo : unit -> unit
  method clear_undo : unit -> unit
  method auto_complete : bool
  method set_auto_complete : bool -> unit
  method right_margin_position : int
  method set_right_margin_position : int -> unit
  method show_right_margin : bool
  method set_show_right_margin : bool -> unit
  method select_all : unit -> unit
  method comment : unit -> unit
  method uncomment : unit -> unit
  method apply_unicode_binding : unit -> unit
  method recenter_insert : unit
  method proposal : string option
  method set_debugging_highlight : int -> int -> unit
  method clear_debugging_highlight : int -> int -> unit
end

val script_view : RocqDriver.rocqtop ->
  ?source_buffer:GSourceView3.source_buffer ->
  ?draw_spaces:SourceView3Enums.source_draw_spaces_flags list ->
  ?auto_indent:bool ->
  ?highlight_current_line:bool ->
  ?indent_on_tab:bool ->
  ?indent_width:int ->
  ?insert_spaces_instead_of_tabs:bool ->
  ?right_margin_position:int ->
  ?show_line_marks:bool ->
  ?show_line_numbers:bool ->
  ?show_right_margin:bool ->
  ?smart_home_end:SourceView3Enums.source_smart_home_end_type ->
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
