(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(*i $Id$ i*)

Require Export Decidable.
Require Export ZAxioms.
Require Import NZMulOrder.

Module ZBasePropFunct (Import ZAxiomsMod : ZAxiomsSig).

(* Note: writing "Export" instead of "Import" on the previous line leads to
some warnings about hiding repeated declarations and results in the loss of
notations in Zadd and later *)

Open Local Scope IntScope.

Module Export NZMulOrderMod := NZMulOrderPropFunct NZOrdAxiomsMod.

Theorem Zsucc_wd : forall n1 n2 : Z, n1 == n2 -> S n1 == S n2.
Proof NZsucc_wd.

Theorem Zpred_wd : forall n1 n2 : Z, n1 == n2 -> P n1 == P n2.
Proof NZpred_wd.

Theorem Zpred_succ : forall n : Z, P (S n) == n.
Proof NZpred_succ.

Theorem Zeq_refl : forall n : Z, n == n.
Proof (proj1 NZeq_equiv).

Theorem Zeq_symm : forall n m : Z, n == m -> m == n.
Proof (proj2 (proj2 NZeq_equiv)).

Theorem Zeq_trans : forall n m p : Z, n == m -> m == p -> n == p.
Proof (proj1 (proj2 NZeq_equiv)).

Theorem Zneq_symm : forall n m : Z, n ~= m -> m ~= n.
Proof NZneq_symm.

Theorem Zsucc_inj : forall n1 n2 : Z, S n1 == S n2 -> n1 == n2.
Proof NZsucc_inj.

Theorem Zsucc_inj_wd : forall n1 n2 : Z, S n1 == S n2 <-> n1 == n2.
Proof NZsucc_inj_wd.

Theorem Zsucc_inj_wd_neg : forall n m : Z, S n ~= S m <-> n ~= m.
Proof NZsucc_inj_wd_neg.

(* Decidability and stability of equality was proved only in NZOrder, but
since it does not mention order, we'll put it here *)

Theorem Zeq_dec : forall n m : Z, decidable (n == m).
Proof NZeq_dec.

Theorem Zeq_dne : forall n m : Z, ~ ~ n == m <-> n == m.
Proof NZeq_dne.

Theorem Zcentral_induction :
forall A : Z -> Prop, predicate_wd Zeq A ->
  forall z : Z, A z ->
    (forall n : Z, A n <-> A (S n)) ->
      forall n : Z, A n.
Proof NZcentral_induction.

(* Theorems that are true for integers but not for natural numbers *)

Theorem Zpred_inj : forall n m : Z, P n == P m -> n == m.
Proof.
intros n m H. apply NZsucc_wd in H. now do 2 rewrite Zsucc_pred in H.
Qed.

Theorem Zpred_inj_wd : forall n1 n2 : Z, P n1 == P n2 <-> n1 == n2.
Proof.
intros n1 n2; split; [apply Zpred_inj | apply NZpred_wd].
Qed.

End ZBasePropFunct.

