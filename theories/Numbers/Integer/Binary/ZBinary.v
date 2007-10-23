Require Import ZTimesOrder.
Require Import ZArith.

Open Local Scope Z_scope.

Module ZBinAxiomsMod <: ZAxiomsSig.
Module Export NZOrdAxiomsMod <: NZOrdAxiomsSig.
Module Export NZAxiomsMod <: NZAxiomsSig.

Definition NZ := Z.
Definition NZeq := (@eq Z).
Definition NZ0 := 0.
Definition NZsucc := Zsucc'.
Definition NZpred := Zpred'.
Definition NZplus := Zplus.
Definition NZminus := Zminus.
Definition NZtimes := Zmult.

Theorem NZE_equiv : equiv Z NZeq.
Proof.
exact (@eq_equiv Z).
Qed.

Add Relation Z NZeq
 reflexivity proved by (proj1 NZE_equiv)
 symmetry proved by (proj2 (proj2 NZE_equiv))
 transitivity proved by (proj1 (proj2 NZE_equiv))
as NZE_rel.

Add Morphism NZsucc with signature NZeq ==> NZeq as NZsucc_wd.
Proof.
congruence.
Qed.

Add Morphism NZpred with signature NZeq ==> NZeq as NZpred_wd.
Proof.
congruence.
Qed.

Add Morphism NZplus with signature NZeq ==> NZeq ==> NZeq as NZplus_wd.
Proof.
congruence.
Qed.

Add Morphism NZminus with signature NZeq ==> NZeq ==> NZeq as NZminus_wd.
Proof.
congruence.
Qed.

Add Morphism NZtimes with signature NZeq ==> NZeq ==> NZeq as NZtimes_wd.
Proof.
congruence.
Qed.

Theorem NZpred_succ : forall n : Z, NZpred (NZsucc n) = n.
Proof.
exact Zpred'_succ'.
Qed.

Theorem NZinduction :
  forall A : Z -> Prop, predicate_wd NZeq A ->
    A 0 -> (forall n : Z, A n <-> A (NZsucc n)) -> forall n : Z, A n.
Proof.
intros A A_wd A0 AS n; apply Zind; clear n.
assumption.
intros; now apply -> AS.
intros n H. rewrite <- (Zsucc'_pred' n) in H. now apply <- AS.
Qed.

Theorem NZplus_0_l : forall n : Z, 0 + n = n.
Proof.
exact Zplus_0_l.
Qed.

Theorem NZplus_succ_l : forall n m : Z, (NZsucc n) + m = NZsucc (n + m).
Proof.
intros; do 2 rewrite <- Zsucc_succ'; apply Zplus_succ_l.
Qed.

Theorem NZminus_0_r : forall n : Z, n - 0 = n.
Proof.
exact Zminus_0_r.
Qed.

Theorem NZminus_succ_r : forall n m : Z, n - (NZsucc m) = NZpred (n - m).
Proof.
intros; rewrite <- Zsucc_succ'; rewrite <- Zpred_pred';
apply Zminus_succ_r.
Qed.

Theorem NZtimes_0_r : forall n : Z, n * 0 = 0.
Proof.
exact Zmult_0_r.
Qed.

Theorem NZtimes_succ_r : forall n m : Z, n * (NZsucc m) = n * m + n.
Proof.
intros; rewrite <- Zsucc_succ'; apply Zmult_succ_r.
Qed.

End NZAxiomsMod.

Definition NZlt := Zlt.
Definition NZle := Zle.

Add Morphism NZlt with signature NZeq ==> NZeq ==> iff as NZlt_wd.
Proof.
unfold NZeq. intros n1 n2 H1 m1 m2 H2; rewrite H1; now rewrite H2.
Qed.

Add Morphism NZle with signature NZeq ==> NZeq ==> iff as NZle_wd.
Proof.
unfold NZeq. intros n1 n2 H1 m1 m2 H2; rewrite H1; now rewrite H2.
Qed.

Theorem NZle_lt_or_eq : forall n m : Z, n <= m <-> n < m \/ n = m.
Proof.
intros n m; split. apply Zle_lt_or_eq.
intro H; destruct H as [H | H]. now apply Zlt_le_weak. rewrite H; apply Zle_refl.
Qed.

Theorem NZlt_irrefl : forall n : Z, ~ n < n.
Proof.
exact Zlt_irrefl.
Qed.

Theorem NZlt_succ_le : forall n m : Z, n < (NZsucc m) <-> n <= m.
Proof.
intros; unfold NZsucc; rewrite <- Zsucc_succ'; split;
[apply Zlt_succ_le | apply Zle_lt_succ].
Qed.

End NZOrdAxiomsMod.

Definition Zopp (x : Z) :=
match x with
| Z0 => Z0
| Zpos x => Zneg x
| Zneg x => Zpos x
end.

Add Morphism Zopp with signature NZeq ==> NZeq as Zopp_wd.
Proof.
congruence.
Qed.

Theorem Zsucc_pred : forall n : Z, NZsucc (NZpred n) = n.
Proof.
exact Zsucc'_pred'.
Qed.

Theorem Zopp_0 : - 0 = 0.
Proof.
reflexivity.
Qed.

Theorem Zopp_succ : forall n : Z, - (NZsucc n) = NZpred (- n).
Proof.
intro; rewrite <- Zsucc_succ'; rewrite <- Zpred_pred'. apply Zopp_succ.
Qed.

End ZBinAxiomsMod.

Module Export ZBinTimesOrderPropMod := ZTimesOrderPropFunct ZBinAxiomsMod.




(*
Theorem E_equiv_e : forall x y : Z, E x y <-> e x y.
Proof.
intros x y; unfold E, e, Zeq_bool; split; intro H.
rewrite H; now rewrite Zcompare_refl.
rewrite eq_true_unfold_pos in H.
assert (H1 : (x ?= y) = Eq).
case_eq (x ?= y); intro H1; rewrite H1 in H; simpl in H;
[reflexivity | discriminate H | discriminate H].
now apply Zcompare_Eq_eq.
Qed.
*)