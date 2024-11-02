(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
Require Import Lia.
Import BinInt.

#[global]
Hint Resolve Z.le_refl Z.add_comm Z.add_assoc Z.mul_comm Z.mul_assoc Z.add_0_l
  Z.add_0_r Z.mul_1_l Z.add_opp_diag_l Z.add_opp_diag_r Z.mul_add_distr_r
  Z.mul_add_distr_l: zarith.

Require Export Zhints.

#[global]
Hint Extern 10 (_ = _ :>nat) => abstract lia: zarith.
#[global]
Hint Extern 10 (_ <= _) => abstract lia: zarith.
#[global]
Hint Extern 10 (_ < _) => abstract lia: zarith.
#[global]
Hint Extern 10 (_ >= _) => abstract lia: zarith.
#[global]
Hint Extern 10 (_ > _) => abstract lia: zarith.

#[global]
Hint Extern 10 (_ <> _ :>nat) => abstract lia: zarith.
#[global]
Hint Extern 10 (~ _ <= _) => abstract lia: zarith.
#[global]
Hint Extern 10 (~ _ < _) => abstract lia: zarith.
#[global]
Hint Extern 10 (~ _ >= _) => abstract lia: zarith.
#[global]
Hint Extern 10 (~ _ > _) => abstract lia: zarith.

#[global]
Hint Extern 10 (_ = _ :>Z) => abstract lia: zarith.
#[global]
Hint Extern 10 (_ <= _)%Z => abstract lia: zarith.
#[global]
Hint Extern 10 (_ < _)%Z => abstract lia: zarith.
#[global]
Hint Extern 10 (_ >= _)%Z => abstract lia: zarith.
#[global]
Hint Extern 10 (_ > _)%Z => abstract lia: zarith.

#[global]
Hint Extern 10 (_ <> _ :>Z) => abstract lia: zarith.
#[global]
Hint Extern 10 (~ (_ <= _)%Z) => abstract lia: zarith.
#[global]
Hint Extern 10 (~ (_ < _)%Z) => abstract lia: zarith.
#[global]
Hint Extern 10 (~ (_ >= _)%Z) => abstract lia: zarith.
#[global]
Hint Extern 10 (~ (_ > _)%Z) => abstract lia: zarith.

#[global]
Hint Extern 10 False => abstract lia: zarith.
