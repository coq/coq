(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

class finder : string -> GText.view ->
  object
    method coerce : GObj.widget
    method hide : unit -> unit
    method show : unit -> unit
    method replace : unit -> unit
    method replace_all : unit -> unit
    method find_backward : unit -> unit
    method find_forward : unit -> unit
  end
