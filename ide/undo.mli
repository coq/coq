(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(* An undoable view class *)

class undoable_view : Gtk.textview Gtk.obj ->
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
  ?wrap_mode:Gtk.Tags.wrap_mode ->
  ?packing:(GObj.widget -> unit) -> ?show:bool -> unit -> undoable_view


