(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
