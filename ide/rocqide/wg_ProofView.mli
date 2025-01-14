(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type goals =
| NoGoals
| FocusGoals of { fg : Interface.goal list; bg : Interface.goal list }
| NoFocusGoals of {
  bg : Interface.goal list;
  shelved : Interface.goal list;
  given_up : Interface.goal list;
}

class type proof_view =
  object
    inherit GObj.widget
    method source_buffer : GSourceView3.source_buffer
    method buffer : GText.buffer
    method select_all : unit -> unit
    method refresh : force:bool -> unit
    method clear : unit -> unit
    method set_goals : goals -> unit
    method set_debug_goal : Pp.t -> unit
  end

val proof_view : unit -> proof_view
