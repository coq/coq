(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Normalisation functions for rational numbers. *)

Require Export QArith_base.

Notation Z2P := Z.to_pos (only parsing).
Notation Z2P_correct := Z2Pos.id (only parsing).

Local Coercion Z.pos : positive >-> Z.

(** Simplification of fractions using [Z.gcd].
  This version can compute within Coq. *)

Definition Qred (q:Q) :=
  let (q1,q2) := q in
  let (r1,r2) := snd (Z.ggcd q1 (Zpos q2))
  in r1#(Z.to_pos r2).

Lemma Qred_correct : forall q, (Qred q) == q.
Proof.
  unfold Qred, Qeq; intros (n,d); simpl.
  generalize (Z.ggcd_gcd n (Zpos d)) (Z.gcd_nonneg n (Zpos d))
    (Z.ggcd_correct_divisors n (Zpos d)).
  destruct (Z.ggcd n (Zpos d)) as (g,(nn,dd)); simpl.
  Open Scope Z_scope.
  intros Hg LE (Hn,Hd). rewrite Hd, Hn.
  rewrite <- Hg in LE; clear Hg.
  assert (0 <> g) by (intro; subst; discriminate).
  rewrite Z2Pos.id.
  - ring.
  - now rewrite <- (Z.mul_pos_cancel_l g); [ rewrite <- Hd | apply Z.le_neq ].
    Close Scope Z_scope.
Qed.

Lemma Qeq_Qred_iff q q' : Qred q == Qred q' <-> q == q'.
Proof. rewrite 2Qred_correct; reflexivity. Qed.

Lemma gcd_Qred q : Z.gcd (Qnum (Qred q)) (Qden (Qred q)) = 1%Z.
Proof.
  case q as [a b]; cbv [Qred Qnum Qden].
  pose proof Z.ggcd_correct_divisors a b as Hg.
  pose proof Z.ggcd_gcd a b as Hgg.
  destruct (Z.ggcd a b) as (g&a'&b'); cbn [fst snd] in *; subst g; case Hg as [Ha Hb].
  assert (Z.gcd a b <> 0)%Z by (rewrite Z.gcd_eq_0; intros []; discriminate).

  erewrite <-(Z.gcd_div_gcd a b); trivial; trivial.
  rewrite Ha, Z.mul_comm, Z.div_mul at 1; trivial.
  rewrite Hb, Z.mul_comm, Z.div_mul at 1; trivial.
  rewrite Z2Pos.id; trivial.
  eapply Z.mul_pos_cancel_l; try rewrite <-Hb; trivial using Pos2Z.is_pos.
  pose proof Z.gcd_nonneg a b as HH; apply Z.le_lteq in HH; intuition congruence.
Qed.

Lemma Qred_complete : forall p q,  p==q -> Qred p = Qred q.
Proof.
  setoid_rewrite <-Qeq_Qred_iff.
  intros a b; specialize (gcd_Qred a); specialize (gcd_Qred b).
  destruct (Qred a) as [p q]; destruct (Qred b) as [p' q'].
  cbv [Qred Qeq Qnum Qden]; intros H H' Hcross.

  pose proof Z.gauss q' p' q ltac:(exists p; ring [Hcross]) ltac:(rewrite Z.gcd_comm; trivial).
  pose proof Z.gauss q p q' ltac:(exists p'; ring [Hcross]) ltac:(rewrite Z.gcd_comm; trivial).
  pose proof Pos2Z.is_nonneg.
  pose proof Z.divide_antisym_nonneg q q' ltac:(trivial) ltac:(trivial) ltac:(trivial) ltac:(trivial) as q'q.
  injection q'q as <-; f_equal. eapply Z.mul_cancel_r with (p:=q); trivial. inversion 1.
Qed.

Lemma Qred_eq_iff q q' : Qred q = Qred q' <-> q == q'.
Proof.
 split.
 - intros E. rewrite <- (Qred_correct q), <- (Qred_correct q').
   now rewrite E.
 - apply Qred_complete.
Qed.

Add Morphism Qred with signature (Qeq ==> Qeq) as Qred_comp.
Proof.
  intros. now rewrite !Qred_correct.
Qed.

Definition Qplus' (p q : Q) := Qred (Qplus p q).
Definition Qmult' (p q : Q) := Qred (Qmult p q).
Definition Qminus' x y := Qred (Qminus x y).

Lemma Qplus'_correct : forall p q : Q, (Qplus' p q)==(Qplus p q).
Proof.
  intros; unfold Qplus'; apply Qred_correct; auto.
Qed.

Lemma Qmult'_correct : forall p q : Q, (Qmult' p q)==(Qmult p q).
Proof.
  intros; unfold Qmult'; apply Qred_correct; auto.
Qed.

Lemma Qminus'_correct : forall p q : Q, (Qminus' p q)==(Qminus p q).
Proof.
  intros; unfold Qminus'; apply Qred_correct; auto.
Qed.

Add Morphism Qplus' with signature (Qeq ==> Qeq ==> Qeq) as Qplus'_comp.
Proof.
  intros ? ? H ? ? H0; unfold Qplus'.
  rewrite H, H0; auto with qarith.
Qed.

Add Morphism Qmult' with signature (Qeq ==> Qeq ==> Qeq) as Qmult'_comp.
Proof.
  intros ? ? H ? ? H0; unfold Qmult'.
  rewrite H, H0; auto with qarith.
Qed.

Add Morphism Qminus' with signature (Qeq ==> Qeq ==> Qeq) as Qminus'_comp.
Proof.
  intros ? ? H ? ? H0; unfold Qminus'.
  rewrite H, H0; auto with qarith.
Qed.

Lemma Qred_opp: forall q, Qred (-q) = - (Qred q).
Proof.
  intros (x, y); unfold Qred; simpl.
  rewrite Z.ggcd_opp; case Z.ggcd; intros p1 (p2, p3); simpl.
  unfold Qopp; auto.
Qed.

Theorem Qred_compare: forall x y,
  Qcompare x y = Qcompare (Qred x) (Qred y).
Proof.
  intros x y; apply Qcompare_comp; apply Qeq_sym; apply Qred_correct.
Qed.

Lemma Qred_le q q' : Qred q <= Qred q' <-> q <= q'.
Proof.
  now rewrite !Qle_alt, <- Qred_compare.
Qed.

Lemma Qred_lt q q' : Qred q < Qred q' <-> q < q'.
Proof.
  now rewrite !Qlt_alt, <- Qred_compare.
Qed.
