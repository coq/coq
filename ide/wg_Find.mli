(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type mode = [ `FIND | `REPLACE ]

class finder : GText.view ->
  object
    method coerce : GObj.widget
    method hide : unit -> unit
    method show : mode -> unit
    method replace : unit -> unit
    method replace_all : unit -> unit
    method find_backward : unit -> unit
    method find_forward : unit -> unit
  end
