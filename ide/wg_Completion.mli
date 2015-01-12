(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module Proposals : sig type t end

class type complete_model_signals =
  object ('a)
    method after : 'a
    method disconnect : GtkSignal.id -> unit
    method start_completion : callback:(int -> unit) -> GtkSignal.id
    method update_completion : callback:(int * string * Proposals.t -> unit) -> GtkSignal.id
    method end_completion : callback:(unit -> unit) -> GtkSignal.id
  end

class complete_model : Coq.coqtop -> GText.buffer ->
object
  method active : bool
  method connect : complete_model_signals
  method set_active : bool -> unit
  method store : GTree.model_filter
  method column : string GTree.column
  method handle_proposal : Gtk.tree_path -> unit
end

class complete_popup : complete_model -> GText.view ->
object
  method coerce : GObj.widget
  method proposal : string option
end
