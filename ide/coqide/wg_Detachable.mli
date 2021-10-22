(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

class type detachable_signals =
  object
    inherit GContainer.container_signals
    method attached : callback:(GObj.widget -> unit) -> unit
    method detached : callback:(GObj.widget -> unit) -> unit
  end

class detachable : ([> Gtk.box] as 'a) Gobject.obj ->
  object
    inherit GPack.box_skel
    val obj : Gtk.box Gobject.obj
    method connect : detachable_signals
    method child : GObj.widget
    method show : unit
    method hide : unit
    method visible : bool
    method title : string
    method set_title : string -> unit
    method button : GButton.button
    method close_button : GButton.button
    method win : GWindow.window
    method frame : GBin.frame
    method detach : unit -> unit
    method attach : unit -> unit
  end

val detachable :
  ?title:string ->
  ?homogeneous:bool ->
  ?spacing:int ->
  ?border_width:int ->
  ?width:int ->
  ?height:int ->
  ?packing:(GObj.widget -> unit) -> ?show:bool -> unit -> detachable


