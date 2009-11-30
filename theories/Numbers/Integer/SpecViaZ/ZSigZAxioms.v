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

Delimit Scope NumScope with Num.
Bind Scope NumScope with Z.t.
Local Open Scope NumScope.
Local Notation "[ x ]" := (Z.to_Z x) : NumScope.
Local Infix "=="  := Z.eq (at level 70) : NumScope.
Local Notation "0" := Z.zero : NumScope.
Local Infix "+" := Z.add : NumScope.
Local Infix "-" := Z.sub : NumScope.
Local Infix "*" := Z.mul : NumScope.
Local Notation "- x" := (Z.opp x) : NumScope.
Local Infix "<=" := Z.le : NumScope.
Local Infix "<" := Z.lt : NumScope.

Hint Rewrite
 Z.spec_0 Z.spec_1 Z.spec_add Z.spec_sub Z.spec_pred Z.spec_succ
 Z.spec_mul Z.spec_opp Z.spec_of_Z : zspec.

Ltac zsimpl := unfold Z.eq in *; autorewrite with zspec.
Ltac zcongruence := repeat red; intros; zsimpl; congruence.

Instance Z_measure: @Measure Z.t Z Z.to_Z.
Instance eq_equiv : Equivalence Z.eq.

Obligation Tactic := zcongruence.

Program Instance succ_wd : Proper (Z.eq ==> Z.eq) Z.succ.
Program Instance pred_wd : Proper (Z.eq ==> Z.eq) Z.pred.
Program Instance add_wd : Proper (Z.eq ==> Z.eq ==> Z.eq) Z.add.
Program Instance sub_wd : Proper (Z.eq ==> Z.eq ==> Z.eq) Z.sub.
Program Instance mul_wd : Proper (Z.eq ==> Z.eq ==> Z.eq) Z.mul.

Theorem pred_succ : forall n, Z.pred (Z.succ n) == n.
Proof.
intros; zsimpl; auto with zarith.
Qed.

Section Induction.

Variable A : Z.t -> Prop.
Hypothesis A_wd : Proper (Z.eq==>iff) A.
Hypothesis A0 : A 0.
Hypothesis AS : forall n, A n <-> A (Z.succ n).

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

Theorem bi_induction : forall n, A n.
Proof.
intro n. setoid_replace n with (Z.of_Z (Z.to_Z n)).
apply B_holds.
zsimpl; auto.
Qed.

End Induction.

Theorem add_0_l : forall n, 0 + n == n.
Proof.
intros; zsimpl; auto with zarith.
Qed.

Theorem add_succ_l : forall n m, (Z.succ n) + m == Z.succ (n + m).
Proof.
intros; zsimpl; auto with zarith.
Qed.

Theorem sub_0_r : forall n, n - 0 == n.
Proof.
intros; zsimpl; auto with zarith.
Qed.

Theorem sub_succ_r : forall n m, n - (Z.succ m) == Z.pred (n - m).
Proof.
intros; zsimpl; auto with zarith.
Qed.

Theorem mul_0_l : forall n, 0 * n == 0.
Proof.
intros; zsimpl; auto with zarith.
Qed.

Theorem mul_succ_l : forall n m, (Z.succ n) * m == n * m + m.
Proof.
intros; zsimpl; ring.
Qed.

(** Order *)

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

Instance compare_wd : Proper (Z.eq ==> Z.eq ==> eq) Z.compare.
Proof.
intros x x' Hx y y' Hy.
rewrite 2 spec_compare_alt; unfold Z.eq in *; rewrite Hx, Hy; intuition.
Qed.

Instance lt_wd : Proper (Z.eq ==> Z.eq ==> iff) Z.lt.
Proof.
intros x x' Hx y y' Hy; unfold Z.lt; rewrite Hx, Hy; intuition.
Qed.

Theorem lt_eq_cases : forall n m, n <= m <-> n < m \/ n == m.
Proof.
intros.
unfold Z.eq; rewrite spec_lt, spec_le; omega.
Qed.

Theorem lt_irrefl : forall n, ~ n < n.
Proof.
intros; rewrite spec_lt; auto with zarith.
Qed.

Theorem lt_succ_r : forall n m, n < (Z.succ m) <-> n <= m.
Proof.
intros; rewrite spec_lt, spec_le, Z.spec_succ; omega.
Qed.

Theorem min_l : forall n m, n <= m -> Z.min n m == n.
Proof.
intros n m; unfold Z.eq; rewrite spec_le, spec_min.
generalize (Zmin_spec [n] [m]); omega.
Qed.

Theorem min_r : forall n m, m <= n -> Z.min n m == m.
Proof.
intros n m; unfold Z.eq; rewrite spec_le, spec_min.
generalize (Zmin_spec [n] [m]); omega.
Qed.

Theorem max_l : forall n m, m <= n -> Z.max n m == n.
Proof.
intros n m; unfold Z.eq; rewrite spec_le, spec_max.
generalize (Zmax_spec [n] [m]); omega.
Qed.

Theorem max_r : forall n m, n <= m -> Z.max n m == m.
Proof.
intros n m; unfold Z.eq; rewrite spec_le, spec_max.
generalize (Zmax_spec [n] [m]); omega.
Qed.

(** Part specific to integers, not natural numbers *)

Program Instance opp_wd : Proper (Z.eq ==> Z.eq) Z.opp.

Theorem succ_pred : forall n, Z.succ (Z.pred n) == n.
Proof.
red; intros; zsimpl; auto with zarith.
Qed.

Theorem opp_0 : - 0 == 0.
Proof.
red; intros; zsimpl; auto with zarith.
Qed.

Theorem opp_succ : forall n, - (Z.succ n) == Z.pred (- n).
Proof.
intros; zsimpl; auto with zarith.
Qed.

(** Aliases *)

Definition t := Z.t.
Definition eq := Z.eq.
Definition zero := Z.zero.
Definition succ := Z.succ.
Definition pred := Z.pred.
Definition add := Z.add.
Definition sub := Z.sub.
Definition mul := Z.mul.
Definition opp := Z.opp.
Definition lt := Z.lt.
Definition le := Z.le.
Definition min := Z.min.
Definition max := Z.max.

End ZSig_ZAxioms.
