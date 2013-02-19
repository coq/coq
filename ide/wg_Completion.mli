(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module Proposals : Set.S with type elt = string

class complete_model : Coq.coqtop -> GText.buffer ->
object
  method active : bool
  method set_active : bool -> unit
  method store : GTree.model
  method column : string GTree.column
  method handle_proposal : Gtk.tree_path -> unit
  method start_completion_callback : (int -> unit) -> unit
  method update_completion_callback : (int -> string -> Proposals.t -> unit) -> unit
  method end_completion_callback : (unit -> unit) -> unit
end

class complete_popup : complete_model -> GText.view ->
object
  method coerce : GObj.widget
end
