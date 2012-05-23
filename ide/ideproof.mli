(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

val display :
  (GText.view -> Interface.goal list -> 'a -> unit) -> GText.view ->
  Interface.goals option -> 'a -> Interface.evar list option -> unit

val mode_tactic :
  ('a -> unit -> unit) -> GText.view -> Interface.goal list ->
  ((string * 'a) list list * (string * 'a) list) option -> unit
