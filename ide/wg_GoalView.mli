(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

class type goal_view =
  object
    inherit GObj.widget
    method buffer : GText.buffer
    method clear : unit -> unit
    method refresh : Interface.goal -> unit
    method width : int
    method view : GText.view_skel
  end

val goal_view : unit -> goal_view
