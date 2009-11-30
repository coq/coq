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

Require Export NZAxioms.
Require Import BigNumPrelude.
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

Definition t := w.

Definition NZ_to_Z : t -> Z := znz_to_Z w_op.
Definition Z_to_NZ : Z -> t := znz_of_Z w_op.
Local Notation wB := (base w_op.(znz_digits)).

Local Notation "[| x |]" := (w_op.(znz_to_Z) x) (at level 0, x at level 99).

Definition eq (n m : t) := [| n |] = [| m |].
Definition zero := w_op.(znz_0).
Definition succ := w_op.(znz_succ).
Definition pred := w_op.(znz_pred).
Definition add := w_op.(znz_add).
Definition sub := w_op.(znz_sub).
Definition mul := w_op.(znz_mul).

Delimit Scope NumScope with Num.
Bind Scope NumScope with t.
Local Open Scope NumScope.
Notation "x == y"  := (eq x y) (at level 70) : NumScope.
Notation "0" := zero : NumScope.
Notation S := succ.
Notation P := pred.
Notation "x + y" := (add x y) : NumScope.
Notation "x - y" := (sub x y) : NumScope.
Notation "x * y" := (mul x y) : NumScope.


Hint Rewrite w_spec.(spec_0) w_spec.(spec_succ) w_spec.(spec_pred)
 w_spec.(spec_add) w_spec.(spec_mul) w_spec.(spec_sub) : w.
Ltac wsimpl :=
 unfold eq, zero, succ, pred, add, sub, mul; autorewrite with w.
Ltac wcongruence := repeat red; intros; wsimpl; congruence.

Instance znz_measure: Measure w_op.(znz_to_Z).
Instance eq_equiv : Equivalence eq.

Instance succ_wd : Proper (eq ==> eq) succ.
Proof.
wcongruence.
Qed.

Instance pred_wd : Proper (eq ==> eq) pred.
Proof.
wcongruence.
Qed.

Instance add_wd : Proper (eq ==> eq ==> eq) add.
Proof.
wcongruence.
Qed.

Instance sub_wd : Proper (eq ==> eq ==> eq) sub.
Proof.
wcongruence.
Qed.

Instance mul_wd : Proper (eq ==> eq ==> eq) mul.
Proof.
wcongruence.
Qed.

Theorem gt_wB_1 : 1 < wB.
Proof.
unfold base. apply Zpower_gt_1; unfold Zlt; auto with zarith.
Qed.

Theorem gt_wB_0 : 0 < wB.
Proof.
pose proof gt_wB_1; auto with zarith.
Qed.

Lemma succ_mod_wB : forall n : Z, (n + 1) mod wB = ((n mod wB) + 1) mod wB.
Proof.
intro n.
pattern 1 at 2. replace 1 with (1 mod wB). rewrite <- Zplus_mod.
reflexivity.
now rewrite Zmod_small; [ | split; [auto with zarith | apply gt_wB_1]].
Qed.

Lemma pred_mod_wB : forall n : Z, (n - 1) mod wB = ((n mod wB) - 1) mod wB.
Proof.
intro n.
pattern 1 at 2. replace 1 with (1 mod wB). rewrite <- Zminus_mod.
reflexivity.
now rewrite Zmod_small; [ | split; [auto with zarith | apply gt_wB_1]].
Qed.

Lemma NZ_to_Z_mod : forall n, [| n |] mod wB = [| n |].
Proof.
intro n; rewrite Zmod_small. reflexivity. apply w_spec.(spec_to_Z).
Qed.

Theorem pred_succ : forall n, P (S n) == n.
Proof.
intro n. wsimpl.
rewrite <- pred_mod_wB.
replace ([| n |] + 1 - 1)%Z with [| n |] by auto with zarith. apply NZ_to_Z_mod.
Qed.

Lemma Z_to_NZ_0 : Z_to_NZ 0%Z == 0%Num.
Proof.
unfold NZ_to_Z, Z_to_NZ. wsimpl.
rewrite znz_of_Z_correct; auto.
exact w_spec. split; [auto with zarith |apply gt_wB_0].
Qed.

Section Induction.

Variable A : t -> Prop.
Hypothesis A_wd : Proper (eq ==> iff) A.
Hypothesis A0 : A 0.
Hypothesis AS : forall n, A n <-> A (S n).
 (* Below, we use only -> direction *)

Let B (n : Z) := A (Z_to_NZ n).

Lemma B0 : B 0.
Proof.
unfold B. now rewrite Z_to_NZ_0.
Qed.

Lemma BS : forall n : Z, 0 <= n -> n < wB - 1 -> B n -> B (n + 1).
Proof.
intros n H1 H2 H3.
unfold B in *. apply -> AS in H3.
setoid_replace (Z_to_NZ (n + 1)) with (S (Z_to_NZ n)). assumption.
wsimpl.
unfold NZ_to_Z, Z_to_NZ.
do 2 (rewrite znz_of_Z_correct; [ | exact w_spec | auto with zarith]).
symmetry; apply Zmod_small; auto with zarith.
Qed.

Lemma B_holds : forall n : Z, 0 <= n < wB -> B n.
Proof.
intros n [H1 H2].
apply Zbounded_induction with wB.
apply B0. apply BS. assumption. assumption.
Qed.

Theorem bi_induction : forall n, A n.
Proof.
intro n. setoid_replace n with (Z_to_NZ (NZ_to_Z n)).
apply B_holds. apply w_spec.(spec_to_Z).
unfold eq, NZ_to_Z, Z_to_NZ; rewrite znz_of_Z_correct.
reflexivity.
exact w_spec.
apply w_spec.(spec_to_Z).
Qed.

End Induction.

Theorem add_0_l : forall n, 0 + n == n.
Proof.
intro n. wsimpl.
rewrite Zplus_0_l. rewrite Zmod_small; [reflexivity | apply w_spec.(spec_to_Z)].
Qed.

Theorem add_succ_l : forall n m, (S n) + m == S (n + m).
Proof.
intros n m. wsimpl.
rewrite succ_mod_wB. repeat rewrite Zplus_mod_idemp_l; try apply gt_wB_0.
rewrite <- (Zplus_assoc ([| n |] mod wB) 1 [| m |]). rewrite Zplus_mod_idemp_l.
rewrite (Zplus_comm 1 [| m |]); now rewrite Zplus_assoc.
Qed.

Theorem sub_0_r : forall n, n - 0 == n.
Proof.
intro n. wsimpl. rewrite Zminus_0_r. apply NZ_to_Z_mod.
Qed.

Theorem sub_succ_r : forall n m, n - (S m) == P (n - m).
Proof.
intros n m. wsimpl. rewrite Zminus_mod_idemp_r, Zminus_mod_idemp_l.
now replace ([|n|] - ([|m|] + 1))%Z with ([|n|] - [|m|] - 1)%Z
     by auto with zarith.
Qed.

Theorem mul_0_l : forall n, 0 * n == 0.
Proof.
intro n. wsimpl. now rewrite Zmult_0_l.
Qed.

Theorem mul_succ_l : forall n m, (S n) * m == n * m + m.
Proof.
intros n m. wsimpl. rewrite Zplus_mod_idemp_l, Zmult_mod_idemp_l.
now rewrite Zmult_plus_distr_l, Zmult_1_l.
Qed.

End NZCyclicAxiomsMod.
