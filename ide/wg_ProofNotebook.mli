(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

class type proof_view =
  object
    inherit GPack.notebook
    method buffer : GText.buffer
    method refresh : unit -> unit
    method clear : unit -> unit
    method set_goals : Interface.goals option -> unit
    method set_evars : Interface.evar list option -> unit
    method width : int
  end

val create : unit -> proof_notebook
