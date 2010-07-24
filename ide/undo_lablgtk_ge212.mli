(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: undo_lablgtk_ge26.mli 7580 2005-11-18 17:09:10Z herbelin $ i*)

(* An undoable view class *)

class undoable_view : ([> Gtk.text_view] as 'a) Gtk.obj ->
object
  inherit GText.view
  val obj : 'a Gtk.obj
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
    ?accepts_tab:bool ->
    ?border_width:int ->
    ?width:int ->
    ?height:int ->
    ?packing:(GObj.widget -> unit) ->
    ?show:bool ->
    unit ->
  undoable_view


