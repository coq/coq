(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

class type proof_view =
  object
    inherit GObj.widget
    method buffer : GText.buffer
    method refresh : force:bool -> unit
    method clear : unit -> unit
    method set_goals : Interface.goals option -> unit
    method set_evars : Interface.evar list option -> unit
  end

val proof_view : unit -> proof_view
