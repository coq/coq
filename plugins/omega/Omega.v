(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(**************************************************************************)
(*                                                                        *)
(* Omega: a solver of quantifier-free problems in Presburger Arithmetic   *)
(*                                                                        *)
(* Pierre Crégut (CNET, Lannion, France)                                  *)
(*                                                                        *)
(**************************************************************************)

(* $Id$ *)

(* We do not require [ZArith] anymore, but only what's necessary for Omega *)
Require Export ZArith_base.
Require Export OmegaLemmas.
Require Export PreOmega.
Declare ML Module "omega_plugin".

Hint Resolve Zle_refl Zplus_comm Zplus_assoc Zmult_comm Zmult_assoc Zplus_0_l
  Zplus_0_r Zmult_1_l Zplus_opp_l Zplus_opp_r Zmult_plus_distr_l
  Zmult_plus_distr_r: zarith.

Require Export Zhints.

(*
(* The constant minus is required in coq_omega.ml *)
Require Minus.
*)

Hint Extern 10 (_ = _ :>nat) => abstract omega: zarith.
Hint Extern 10 (_ <= _) => abstract omega: zarith.
Hint Extern 10 (_ < _) => abstract omega: zarith.
Hint Extern 10 (_ >= _) => abstract omega: zarith.
Hint Extern 10 (_ > _) => abstract omega: zarith.

Hint Extern 10 (_ <> _ :>nat) => abstract omega: zarith.
Hint Extern 10 (~ _ <= _) => abstract omega: zarith.
Hint Extern 10 (~ _ < _) => abstract omega: zarith.
Hint Extern 10 (~ _ >= _) => abstract omega: zarith.
Hint Extern 10 (~ _ > _) => abstract omega: zarith.

Hint Extern 10 (_ = _ :>Z) => abstract omega: zarith.
Hint Extern 10 (_ <= _)%Z => abstract omega: zarith.
Hint Extern 10 (_ < _)%Z => abstract omega: zarith.
Hint Extern 10 (_ >= _)%Z => abstract omega: zarith.
Hint Extern 10 (_ > _)%Z => abstract omega: zarith.

Hint Extern 10 (_ <> _ :>Z) => abstract omega: zarith.
Hint Extern 10 (~ (_ <= _)%Z) => abstract omega: zarith.
Hint Extern 10 (~ (_ < _)%Z) => abstract omega: zarith.
Hint Extern 10 (~ (_ >= _)%Z) => abstract omega: zarith.
Hint Extern 10 (~ (_ > _)%Z) => abstract omega: zarith.

Hint Extern 10 False => abstract omega: zarith.