(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* An undoable view class *)

class undoable_view : Gtk.text_view Gtk.obj ->
object
  inherit GText.view
  method undo : bool
  method redo : bool
  method clear_undo : unit
end

val undoable_view : 
    ?buffer:GText.buffer ->
    ?editable:bool ->
    ?cursor_visible:bool ->
    ?justification:GtkEnums.justification ->
    ?wrap_mode:GtkEnums.wrap_mode ->
    ?border_width:int ->
    ?width:int ->
    ?height:int ->
    ?packing:(GObj.widget -> unit) ->
    ?show:bool ->
    unit ->
  undoable_view


