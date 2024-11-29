(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2016                             *)
(*                                                                      *)
(************************************************************************)

Require Import ZMicromega.
Require Import QMicromega.
Require Import RMicromega.
Require Import QArith.
Require Import ZArith.
Require Import Rdefinitions.
Require Import RingMicromega.
Require Import VarMap.
Require Stdlib.micromega.Tauto.
Require Lia.
Require Lra.
Require Lqa.

Declare ML Module "rocq-runtime.plugins.micromega".

Ltac lia := Lia.lia.

Ltac nia := Lia.nia.

Ltac xpsatz dom d :=
  let tac := lazymatch dom with
  | Z => (xsos_Z Lia.zchecker) || (xpsatz_Z d Lia.zchecker)
  | R => (xsos_R Lra.rchecker) || (xpsatz_R d Lra.rchecker)
  | Q => (xsos_Q Lqa.rchecker) || (xpsatz_Q d Lqa.rchecker)
  | _ => fail "Unsupported domain"
  end in tac.

Tactic Notation "psatz" constr(dom) int_or_var(n) := xpsatz dom n.
Tactic Notation "psatz" constr(dom) := xpsatz dom ltac:(-1).

Ltac psatzl dom :=
  let tac := lazymatch dom with
  | Z => Lia.lia
  | Q => Lqa.lra
  | R => Lra.lra
  | _ => fail "Unsupported domain"
  end in tac.

Ltac lra :=
  first [ psatzl R | psatzl Q ].

Ltac nra :=
  first [ Lra.nra | Lqa.nra ].

(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
