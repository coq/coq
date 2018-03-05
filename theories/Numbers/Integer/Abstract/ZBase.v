(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Export Decidable.
Require Export ZAxioms.
Require Import NZProperties.

Module ZBaseProp (Import Z : ZAxiomsMiniSig').
Include NZProp Z.

(* Theorems that are true for integers but not for natural numbers *)

Theorem pred_inj : forall n m, P n == P m -> n == m.
Proof.
intros n m H. apply succ_wd in H. now rewrite 2 succ_pred in H.
Qed.

Theorem pred_inj_wd : forall n1 n2, P n1 == P n2 <-> n1 == n2.
Proof.
intros n1 n2; split; [apply pred_inj | intros; now f_equiv].
Qed.

Lemma succ_m1 : S (-1) == 0.
Proof.
 now rewrite one_succ, opp_succ, opp_0, succ_pred.
Qed.

End ZBaseProp.

