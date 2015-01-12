(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type color = GDraw.color

class segment : unit ->
  object
    inherit GObj.widget
    val obj : Gtk.widget Gtk.obj
    method length : int
    method set_length : int -> unit
    method default_color : color
    method set_default_color : color -> unit
    method add : int -> color -> unit
    method remove : int -> unit
  end
