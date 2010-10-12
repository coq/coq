(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Export Decidable.
Require Export ZAxioms.
Require Import NZProperties.

Module ZBasePropFunct (Import Z : ZAxiomsSig').
Include NZPropFunct Z.

(* Theorems that are true for integers but not for natural numbers *)

Theorem pred_inj : forall n m, P n == P m -> n == m.
Proof.
intros n m H. apply succ_wd in H. now do 2 rewrite succ_pred in H.
Qed.

Theorem pred_inj_wd : forall n1 n2, P n1 == P n2 <-> n1 == n2.
Proof.
intros n1 n2; split; [apply pred_inj | apply pred_wd].
Qed.

End ZBasePropFunct.

