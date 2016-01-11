(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

class type proof_notebook =
  object
    inherit GPack.notebook
    method clear : unit -> unit
    method refresh : unit -> unit
    method set_goals : Interface.goals option -> unit
    method set_evars : Interface.evar list option -> unit
  end

val create :
  (Pp.message_level -> string -> unit) ->
  ?enable_popup:bool ->
  ?homogeneous_tabs:bool ->
  ?scrollable:bool ->
  ?show_border:bool ->
  ?show_tabs:bool ->
  ?tab_border:int ->
  ?tab_pos:Gtk.Tags.position ->
  ?border_width:int ->
  ?width:int ->
  ?height:int ->
  ?packing:(GObj.widget -> unit) -> ?show:bool -> unit -> proof_notebook
