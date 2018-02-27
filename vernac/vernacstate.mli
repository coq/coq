(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t = {
  system  : States.state;        (* summary + libstack *)
  proof   : Proof_global.t;      (* proof state *)
  shallow : bool                 (* is the state trimmed down (libstack) *)
}

val freeze_interp_state : Summary.marshallable -> t
val unfreeze_interp_state : t -> unit

(* WARNING: Do not use, it will go away in future releases *)
val invalidate_cache : unit -> unit
