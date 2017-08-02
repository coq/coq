(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Tactics
open Tacmach.New
open Tacticals.New
open Proofview.Notations

(** FIXME: export a better interface in Tactics *)
let delayed_of_tactic tac env sigma =
  let _, pv = Proofview.init sigma [] in
  let c, pv, _, _ = Proofview.apply env tac pv in
  (sigma, c)

let apply adv ev cb cl =
  let map c = None, Loc.tag (delayed_of_tactic c) in
  let cb = List.map map cb in
  match cl with
  | None -> Tactics.apply_with_delayed_bindings_gen adv ev cb
  | Some (id, cl) -> Tactics.apply_delayed_in adv ev id cb cl
