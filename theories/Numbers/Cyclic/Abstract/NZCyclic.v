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

Require Export NZAxioms.
Require Import ZArith.
Require Import Zpow_facts.
Require Import DoubleType.
Require Import CyclicAxioms.

(** * From [CyclicType] to [NZAxiomsSig] *)

(** A [Z/nZ] representation given by a module type [CyclicType]
    implements [NZAxiomsSig], e.g. the common properties between
    N and Z with no ordering. Notice that the [n] in [Z/nZ] is
    a power of 2.
*)

Module NZCyclicAxiomsMod (Import Cyclic : CyclicType) <: NZAxiomsSig.

Local Open Scope Z_scope.

Local Notation wB := (base ZnZ.digits).

Local Notation "[| x |]" := (ZnZ.to_Z x) (at level 0, x at level 99).

Definition eq (n m : t) := [| n |] = [| m |].
Definition zero := ZnZ.zero.
Definition one := ZnZ.one.
Definition two := ZnZ.succ ZnZ.one.
Definition succ := ZnZ.succ.
Definition pred := ZnZ.pred.
Definition add := ZnZ.add.
Definition sub := ZnZ.sub.
Definition mul := ZnZ.mul.

Local Infix "=="  := eq (at level 70).
Local Notation "0" := zero.
Local Notation S := succ.
Local Notation P := pred.
Local Infix "+" := add.
Local Infix "-" := sub.
Local Infix "*" := mul.

Hint Rewrite ZnZ.spec_0 ZnZ.spec_1 ZnZ.spec_succ ZnZ.spec_pred
 ZnZ.spec_add ZnZ.spec_mul ZnZ.spec_sub : cyclic.
Ltac zify :=
 unfold eq, zero, one, two, succ, pred, add, sub, mul in *;
 autorewrite with cyclic.
Ltac zcongruence := repeat red; intros; zify; congruence.

Instance eq_equiv : Equivalence eq.
Proof.
unfold eq. firstorder.
Qed.

Local Obligation Tactic := zcongruence.

Program Instance succ_wd : Proper (eq ==> eq) succ.
Program Instance pred_wd : Proper (eq ==> eq) pred.
Program Instance add_wd : Proper (eq ==> eq ==> eq) add.
Program Instance sub_wd : Proper (eq ==> eq ==> eq) sub.
Program Instance mul_wd : Proper (eq ==> eq ==> eq) mul.

Theorem gt_wB_1 : 1 < wB.
Proof.
unfold base. apply Zpower_gt_1; unfold Z.lt; auto with zarith.
Qed.

Theorem gt_wB_0 : 0 < wB.
Proof.
pose proof gt_wB_1; auto with zarith.
Qed.

Lemma one_mod_wB : 1 mod wB = 1.
Proof.
rewrite Zmod_small. reflexivity. split. auto with zarith. apply gt_wB_1.
Qed.

Lemma succ_mod_wB : forall n : Z, (n + 1) mod wB = ((n mod wB) + 1) mod wB.
Proof.
intro n. rewrite <- one_mod_wB at 2. now rewrite <- Zplus_mod.
Qed.

Lemma pred_mod_wB : forall n : Z, (n - 1) mod wB = ((n mod wB) - 1) mod wB.
Proof.
intro n. rewrite <- one_mod_wB at 2. now rewrite Zminus_mod.
Qed.

Lemma NZ_to_Z_mod : forall n, [| n |] mod wB = [| n |].
Proof.
intro n; rewrite Zmod_small. reflexivity. apply ZnZ.spec_to_Z.
Qed.

Theorem pred_succ : forall n, P (S n) == n.
Proof.
intro n. zify.
rewrite <- pred_mod_wB.
replace ([| n |] + 1 - 1)%Z with [| n |] by ring. apply NZ_to_Z_mod.
Qed.

Theorem one_succ : one == succ zero.
Proof.
zify; simpl Z.add. now rewrite one_mod_wB.
Qed.

Theorem two_succ : two == succ one.
Proof.
reflexivity.
Qed.

Section Induction.

Variable A : t -> Prop.
Hypothesis A_wd : Proper (eq ==> iff) A.
Hypothesis A0 : A 0.
Hypothesis AS : forall n, A n <-> A (S n).
 (* Below, we use only -> direction *)

Let B (n : Z) := A (ZnZ.of_Z n).

Lemma B0 : B 0.
Proof.
unfold B. apply A0.
Qed.

Lemma BS : forall n : Z, 0 <= n -> n < wB - 1 -> B n -> B (n + 1).
Proof.
intros n H1 H2 H3.
unfold B in *. apply AS in H3.
setoid_replace (ZnZ.of_Z (n + 1)) with (S (ZnZ.of_Z n)). assumption.
zify.
rewrite 2 ZnZ.of_Z_correct; auto with zarith.
symmetry; apply Zmod_small; auto with zarith.
Qed.

Theorem Zbounded_induction :
  (forall Q : Z -> Prop, forall b : Z,
    Q 0 ->
    (forall n, 0 <= n -> n < b - 1 -> Q n -> Q (n + 1)) ->
      forall n, 0 <= n -> n < b -> Q n)%Z.
Proof.
intros Q b Q0 QS.
set (Q' := fun n => (n < b /\ Q n) \/ (b <= n)).
assert (H : forall n, 0 <= n -> Q' n).
apply natlike_rec2; unfold Q'.
destruct (Z.le_gt_cases b 0) as [H | H]. now right. left; now split.
intros n H IH. destruct IH as [[IH1 IH2] | IH].
destruct (Z.le_gt_cases (b - 1) n) as [H1 | H1].
right; auto with zarith.
left. split; [auto with zarith | now apply (QS n)].
right; auto with zarith.
unfold Q' in *; intros n H1 H2. destruct (H n H1) as [[H3 H4] | H3].
assumption. now apply Z.le_ngt in H3.
Qed.

Lemma B_holds : forall n : Z, 0 <= n < wB -> B n.
Proof.
intros n [H1 H2].
apply Zbounded_induction with wB.
apply B0. apply BS. assumption. assumption.
Qed.

Theorem bi_induction : forall n, A n.
Proof.
intro n. setoid_replace n with (ZnZ.of_Z (ZnZ.to_Z n)).
apply B_holds. apply ZnZ.spec_to_Z.
red. symmetry. apply ZnZ.of_Z_correct.
apply ZnZ.spec_to_Z.
Qed.

End Induction.

Theorem add_0_l : forall n, 0 + n == n.
Proof.
intro n. zify.
rewrite Z.add_0_l. apply Zmod_small. apply ZnZ.spec_to_Z.
Qed.

Theorem add_succ_l : forall n m, (S n) + m == S (n + m).
Proof.
intros n m. zify.
rewrite succ_mod_wB. repeat rewrite Zplus_mod_idemp_l; try apply gt_wB_0.
rewrite <- (Z.add_assoc ([| n |] mod wB) 1 [| m |]). rewrite Zplus_mod_idemp_l.
rewrite (Z.add_comm 1 [| m |]); now rewrite Z.add_assoc.
Qed.

Theorem sub_0_r : forall n, n - 0 == n.
Proof.
intro n. zify. rewrite Z.sub_0_r. apply NZ_to_Z_mod.
Qed.

Theorem sub_succ_r : forall n m, n - (S m) == P (n - m).
Proof.
intros n m. zify. rewrite Zminus_mod_idemp_r, Zminus_mod_idemp_l.
now replace ([|n|] - ([|m|] + 1))%Z with ([|n|] - [|m|] - 1)%Z
     by ring.
Qed.

Theorem mul_0_l : forall n, 0 * n == 0.
Proof.
intro n. now zify.
Qed.

Theorem mul_succ_l : forall n m, (S n) * m == n * m + m.
Proof.
intros n m. zify. rewrite Zplus_mod_idemp_l, Zmult_mod_idemp_l.
now rewrite Z.mul_add_distr_r, Z.mul_1_l.
Qed.

Definition t := t.

End NZCyclicAxiomsMod.
