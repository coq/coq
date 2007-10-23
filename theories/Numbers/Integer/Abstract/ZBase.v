Require Export ZAxioms.
Require Import NZTimesOrder.

Module ZBasePropFunct (Export ZAxiomsMod : ZAxiomsSig).

Open Local Scope IntScope.

Module Export NZTimesOrderMod := NZTimesOrderPropFunct NZOrdAxiomsMod.

Theorem Zpred_succ : forall n : Z, P (S n) == n.
Proof NZpred_succ.

Theorem Zneq_symm : forall n m : Z, n ~= m -> m ~= n.
Proof NZneq_symm.

Theorem Zsucc_inj : forall n1 n2 : Z, S n1 == S n2 -> n1 == n2.
Proof NZsucc_inj.

Theorem Zsucc_inj_wd : forall n1 n2 : Z, S n1 == S n2 <-> n1 == n2.
Proof NZsucc_inj_wd.

Theorem Zsucc_inj_wd_neg : forall n m : Z, S n ~= S m <-> n ~= m.
Proof NZsucc_inj_wd_neg.

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

