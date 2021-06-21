(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

class debugger : string ->
  object
(*    inherit GPack.box_skel*)
    method coerce : GObj.widget
    method hide : unit -> unit
    method show : unit -> unit
(*    method set_stack : (string * int) list -> unit*)
(*    method set_vars : (string * string) list -> unit*)
  end
