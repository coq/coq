Require Export ZBase.
(*Require Import BigN.*)
Require Import NMake.
Require Import ZnZ.
Require Import Basic_type.
Require Import ZAux.
Require Import Zeqmod.
Require Import ZArith.

Module EZBaseMod (Import EffIntsMod : W0Type) <: ZBaseSig.
Open Local Scope Z_scope.

Definition Z := EffIntsMod.w.

Definition w_op := EffIntsMod.w_op.
Definition w_spec := EffIntsMod.w_spec.
Definition to_Z := w_op.(znz_to_Z).
Definition of_Z := znz_of_Z w_op.
Definition wB := base w_op.(znz_digits).

Theorem Zpow_gt_1 : forall n m : BinInt.Z, 0 < n -> 1 < m -> 1 < m ^ n.
Proof.
intros n m H1 H2.
replace 1 with (m ^ 0) by apply Zpower_exp_0.
apply Zpower_lt_monotone; auto with zarith.
Qed.

Theorem wB_gt_1 : 1 < wB.
Proof.
unfold wB, base. apply Zpow_gt_1; unfold Zlt; auto with zarith.
Qed.

Theorem wB_gt_0 : 0 < wB.
Proof.
pose proof wB_gt_1; auto with zarith.
Qed.

Notation "[| x |]" := (to_Z x) (at level 0, x at level 99).

Theorem to_Z_spec : forall x : Z, 0 <= [|x|] < wB.
Proof w_spec.(spec_to_Z).

Definition ZE (n m : Z) := [|n|] = [|m|].

Notation "x == y"  := (ZE x y) (at level 70) : IntScope.
Notation "x ~= y" := (~ ZE x y) (at level 70) : IntScope.
Open Local Scope IntScope.

Theorem ZE_equiv : equiv Z ZE.
Proof.
unfold equiv, reflexive, symmetric, transitive, ZE; repeat split; intros; auto.
now transitivity [|y|].
Qed.

Add Relation Z ZE
 reflexivity proved by (proj1 ZE_equiv)
 symmetry proved by (proj2 (proj2 ZE_equiv))
 transitivity proved by (proj1 (proj2 ZE_equiv))
as ZE_rel.

Definition Z0 := w_op.(znz_0).
Definition Zsucc := w_op.(znz_succ).

Notation "0" := Z0 : IntScope.
Notation "'S'" := Zsucc : IntScope.
Notation "1" := (S 0) : IntScope.

Theorem Zsucc_spec : forall n : Z, [|S n|] = ([|n|] + 1) mod wB.
Proof w_spec.(spec_succ).

Add Morphism Zsucc with signature ZE ==> ZE as Zsucc_wd.
Proof.
unfold ZE; intros n m H. do 2 rewrite Zsucc_spec. now rewrite H.
Qed.

Theorem Zsucc_inj : forall x y : Z, S x == S y -> x == y.
Proof.
intros x y H; unfold ZE in *; do 2 rewrite Zsucc_spec in H.
apply <- Zplus_eqmod_compat_r in H.
do 2 rewrite Zmod_def_small in H; now try apply to_Z_spec.
apply wB_gt_0.
Qed.

Lemma of_Z_0 : of_Z 0 == Z0.
Proof.
unfold ZE, to_Z, of_Z. rewrite znz_of_Z_correct.
symmetry; apply w_spec.(spec_0).
exact w_spec. split; [auto with zarith |apply wB_gt_0].
Qed.

Section Induction.

Variable A : Z -> Prop.
Hypothesis A_wd : predicate_wd ZE A.
Hypothesis A0 : A 0.
Hypothesis AS : forall n : Z, A n <-> A (S n). (* In fact, it's enought to have only -> *)

Add Morphism A with signature ZE ==> iff as A_morph.
Proof A_wd.

Let B (n : BinInt.Z) := A (of_Z n).

Lemma B0 : B 0.
Proof.
unfold B. now rewrite of_Z_0.
Qed.

Lemma BS : forall n : BinInt.Z, 0 <= n -> n < wB - 1 -> B n -> B (n + 1).
Proof.
intros n H1 H2 H3.
unfold B in *. apply -> AS in H3.
setoid_replace (of_Z (n + 1)) with (S (of_Z n)) using relation ZE. assumption.
unfold ZE. rewrite Zsucc_spec.
unfold to_Z, of_Z. rewrite znz_of_Z_correct. rewrite znz_of_Z_correct.
symmetry; apply Zmod_def_small; auto with zarith.
exact w_spec.
unfold wB in *; auto with zarith.
exact w_spec.
unfold wB in *; auto with zarith.
Qed.

Lemma Zbounded_induction :
  (forall Q : BinInt.Z -> Prop, forall b : BinInt.Z,
    Q 0 ->
    (forall n, 0 <= n -> n < b - 1 -> Q n -> Q (n + 1)) ->
      forall n, 0 <= n -> n < b -> Q n)%Z.
Proof.
intros Q b Q0 QS.
set (Q' := fun n => (n < b /\ Q n) \/ (b <= n)).
assert (H : forall n, 0 <= n -> Q' n).
apply natlike_rec2; unfold Q'.
destruct (Zle_or_lt b 0) as [H | H]. now right. left; now split.
intros n H IH. destruct IH as [[IH1 IH2] | IH].
destruct (Zle_or_lt (b - 1) n) as [H1 | H1].
right; auto with zarith.
left. split; [auto with zarith | now apply (QS n)].
right; auto with zarith.
unfold Q' in *; intros n H1 H2. destruct (H n H1) as [[H3 H4] | H3].
assumption. apply Zle_not_lt in H3. false_hyp H2 H3.
Qed.

Lemma B_holds : forall n : BinInt.Z, 0 <= n < wB -> B n.
Proof.
intros n [H1 H2].
apply Zbounded_induction with wB.
apply B0. apply BS. assumption. assumption.
Qed.

Theorem Zinduction : forall n : Z, A n.
Proof.
intro n. setoid_replace n with (of_Z (to_Z n)) using relation ZE.
apply B_holds. apply to_Z_spec.
unfold ZE, to_Z, of_Z; rewrite znz_of_Z_correct.
reflexivity.
exact w_spec.
apply to_Z_spec.
Qed.

End Induction.

End EZBaseMod.
