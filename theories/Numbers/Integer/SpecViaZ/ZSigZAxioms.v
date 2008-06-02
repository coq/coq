(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import ZArith.
Require Import ZAxioms.
Require Import ZSig.

(** * The interface [ZSig.ZType] implies the interface [ZAxiomsSig] *)

Module ZSig_ZAxioms (Z:ZType) <: ZAxiomsSig.

Delimit Scope IntScope with Int.
Bind Scope IntScope with Z.t.
Open Local Scope IntScope.
Notation "[ x ]" := (Z.to_Z x) : IntScope.
Infix "=="  := Z.eq (at level 70) : IntScope.
Notation "0" := Z.zero : IntScope.
Infix "+" := Z.add : IntScope.
Infix "-" := Z.sub : IntScope.
Infix "*" := Z.mul : IntScope.
Notation "- x" := (Z.opp x) : IntScope.

Hint Rewrite 
 Z.spec_0 Z.spec_1 Z.spec_add Z.spec_sub Z.spec_pred Z.spec_succ
 Z.spec_mul Z.spec_opp Z.spec_of_Z : Zspec.

Ltac zsimpl := unfold Z.eq in *; autorewrite with Zspec.

Module Export NZOrdAxiomsMod <: NZOrdAxiomsSig.
Module Export NZAxiomsMod <: NZAxiomsSig.

Definition NZ := Z.t.
Definition NZeq := Z.eq.
Definition NZ0 := Z.zero.
Definition NZsucc := Z.succ.
Definition NZpred := Z.pred.
Definition NZadd := Z.add.
Definition NZminus := Z.sub.
Definition NZmul := Z.mul.

Theorem NZeq_equiv : equiv Z.t Z.eq.
Proof.
repeat split; repeat red; intros; auto; congruence.
Qed.

Add Relation Z.t Z.eq
 reflexivity proved by (proj1 NZeq_equiv)
 symmetry proved by (proj2 (proj2 NZeq_equiv))
 transitivity proved by (proj1 (proj2 NZeq_equiv))
 as NZeq_rel.

Add Morphism NZsucc with signature Z.eq ==> Z.eq as NZsucc_wd.
Proof.
intros; zsimpl; f_equal; assumption.
Qed.

Add Morphism NZpred with signature Z.eq ==> Z.eq as NZpred_wd.
Proof.
intros; zsimpl; f_equal; assumption.
Qed.

Add Morphism NZadd with signature Z.eq ==> Z.eq ==> Z.eq as NZadd_wd.
Proof.
intros; zsimpl; f_equal; assumption.
Qed.

Add Morphism NZminus with signature Z.eq ==> Z.eq ==> Z.eq as NZminus_wd.
Proof.
intros; zsimpl; f_equal; assumption.
Qed.

Add Morphism NZmul with signature Z.eq ==> Z.eq ==> Z.eq as NZmul_wd.
Proof.
intros; zsimpl; f_equal; assumption.
Qed.

Theorem NZpred_succ : forall n, Z.pred (Z.succ n) == n.
Proof.
intros; zsimpl; auto with zarith.
Qed.

Section Induction.

Variable A : Z.t -> Prop.
Hypothesis A_wd : predicate_wd Z.eq A.
Hypothesis A0 : A 0.
Hypothesis AS : forall n, A n <-> A (Z.succ n). 

Add Morphism A with signature Z.eq ==> iff as A_morph.
Proof. apply A_wd. Qed.

Let B (z : Z) := A (Z.of_Z z).

Lemma B0 : B 0.
Proof.
unfold B; simpl.
rewrite <- (A_wd 0); auto.
zsimpl; auto.
Qed.

Lemma BS : forall z : Z, B z -> B (z + 1).
Proof.
intros z H.
unfold B in *. apply -> AS in H.
setoid_replace (Z.of_Z (z + 1)) with (Z.succ (Z.of_Z z)); auto.
zsimpl; auto.
Qed.

Lemma BP : forall z : Z, B z -> B (z - 1).
Proof.
intros z H.
unfold B in *. rewrite AS.
setoid_replace (Z.succ (Z.of_Z (z - 1))) with (Z.of_Z z); auto.
zsimpl; auto with zarith.
Qed.

Lemma B_holds : forall z : Z, B z.
Proof.
intros; destruct (Z_lt_le_dec 0 z).
apply natlike_ind; auto with zarith.
apply B0.
intros; apply BS; auto.
replace z with (-(-z))%Z in * by (auto with zarith).
remember (-z)%Z as z'.
pattern z'; apply natlike_ind.
apply B0.
intros; rewrite Zopp_succ; unfold Zpred; apply BP; auto.
subst z'; auto with zarith.
Qed.

Theorem NZinduction : forall n, A n.
Proof.
intro n. setoid_replace n with (Z.of_Z (Z.to_Z n)).
apply B_holds.
zsimpl; auto.
Qed.

End Induction.

Theorem NZadd_0_l : forall n, 0 + n == n.
Proof.
intros; zsimpl; auto with zarith.
Qed.

Theorem NZadd_succ_l : forall n m, (Z.succ n) + m == Z.succ (n + m).
Proof.
intros; zsimpl; auto with zarith.
Qed.

Theorem NZminus_0_r : forall n, n - 0 == n.
Proof.
intros; zsimpl; auto with zarith.
Qed.

Theorem NZminus_succ_r : forall n m, n - (Z.succ m) == Z.pred (n - m).
Proof.
intros; zsimpl; auto with zarith.
Qed.

Theorem NZmul_0_l : forall n, 0 * n == 0.
Proof.
intros; zsimpl; auto with zarith.
Qed.

Theorem NZmul_succ_l : forall n m, (Z.succ n) * m == n * m + m.
Proof.
intros; zsimpl; ring.
Qed.

End NZAxiomsMod.

Definition NZlt := Z.lt.
Definition NZle := Z.le.
Definition NZmin := Z.min.
Definition NZmax := Z.max.

Infix "<=" := Z.le : IntScope.
Infix "<" := Z.lt : IntScope.

Lemma spec_compare_alt : forall x y, Z.compare x y = ([x] ?= [y])%Z.
Proof.
 intros; generalize (Z.spec_compare x y).
 destruct (Z.compare x y); auto.
 intros H; rewrite H; symmetry; apply Zcompare_refl.
Qed.

Lemma spec_lt : forall x y, (x<y) <-> ([x]<[y])%Z.
Proof.
 intros; unfold Z.lt, Zlt; rewrite spec_compare_alt; intuition.
Qed.

Lemma spec_le : forall x y, (x<=y) <-> ([x]<=[y])%Z.
Proof.
 intros; unfold Z.le, Zle; rewrite spec_compare_alt; intuition.
Qed.

Lemma spec_min : forall x y, [Z.min x y] = Zmin [x] [y].
Proof.
 intros; unfold Z.min, Zmin.
 rewrite spec_compare_alt; destruct Zcompare; auto.
Qed.

Lemma spec_max : forall x y, [Z.max x y] = Zmax [x] [y].
Proof.
 intros; unfold Z.max, Zmax.
 rewrite spec_compare_alt; destruct Zcompare; auto.
Qed.

Add Morphism Z.compare with signature Z.eq ==> Z.eq ==> (@eq comparison) as compare_wd.
Proof. 
intros x x' Hx y y' Hy.
rewrite 2 spec_compare_alt; rewrite Hx, Hy; intuition.
Qed.

Add Morphism Z.lt with signature Z.eq ==> Z.eq ==> iff as NZlt_wd.
Proof.
intros x x' Hx y y' Hy; unfold Z.lt; rewrite Hx, Hy; intuition.
Qed.

Add Morphism Z.le with signature Z.eq ==> Z.eq ==> iff as NZle_wd.
Proof.
intros x x' Hx y y' Hy; unfold Z.le; rewrite Hx, Hy; intuition.
Qed.

Add Morphism Z.min with signature Z.eq ==> Z.eq ==> Z.eq as NZmin_wd.
Proof.
intros; red; rewrite 2 spec_min; congruence.
Qed.

Add Morphism Z.max with signature Z.eq ==> Z.eq ==> Z.eq as NZmax_wd.
Proof.
intros; red; rewrite 2 spec_max; congruence.
Qed.

Theorem NZlt_eq_cases : forall n m, n <= m <-> n < m \/ n == m.
Proof.
intros.
unfold Z.eq; rewrite spec_lt, spec_le; omega.
Qed.

Theorem NZlt_irrefl : forall n, ~ n < n.
Proof.
intros; rewrite spec_lt; auto with zarith.
Qed.

Theorem NZlt_succ_r : forall n m, n < (Z.succ m) <-> n <= m.
Proof.
intros; rewrite spec_lt, spec_le, Z.spec_succ; omega.
Qed.

Theorem NZmin_l : forall n m, n <= m -> Z.min n m == n.
Proof.
intros n m; unfold Z.eq; rewrite spec_le, spec_min.
generalize (Zmin_spec [n] [m]); omega.
Qed.

Theorem NZmin_r : forall n m, m <= n -> Z.min n m == m.
Proof.
intros n m; unfold Z.eq; rewrite spec_le, spec_min.
generalize (Zmin_spec [n] [m]); omega.
Qed.

Theorem NZmax_l : forall n m, m <= n -> Z.max n m == n.
Proof.
intros n m; unfold Z.eq; rewrite spec_le, spec_max.
generalize (Zmax_spec [n] [m]); omega.
Qed.

Theorem NZmax_r : forall n m, n <= m -> Z.max n m == m.
Proof.
intros n m; unfold Z.eq; rewrite spec_le, spec_max.
generalize (Zmax_spec [n] [m]); omega.
Qed.

End NZOrdAxiomsMod.

Definition Zopp := Z.opp.

Add Morphism Z.opp with signature Z.eq ==> Z.eq as Zopp_wd.
Proof.
intros; zsimpl; auto with zarith.
Qed.

Theorem Zsucc_pred : forall n, Z.succ (Z.pred n) == n.
Proof.
red; intros; zsimpl; auto with zarith.
Qed.

Theorem Zopp_0 : - 0 == 0.
Proof.
red; intros; zsimpl; auto with zarith.
Qed.

Theorem Zopp_succ : forall n, - (Z.succ n) == Z.pred (- n).
Proof.
intros; zsimpl; auto with zarith.
Qed.

End ZSig_ZAxioms.
