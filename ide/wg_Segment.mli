(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type color = GDraw.color

class type segment_signals =
object
  inherit GObj.misc_signals
  inherit GUtil.add_ml_signals
  method clicked : callback:(int -> unit) -> GtkSignal.id
end

class segment : unit ->
  object
    inherit GObj.widget
    val obj : Gtk.widget Gtk.obj
    method connect : segment_signals
    method length : int
    method set_length : int -> unit
    method default_color : color
    method set_default_color : color -> unit
    method add : int -> color -> unit
    method remove : int -> unit
  end
