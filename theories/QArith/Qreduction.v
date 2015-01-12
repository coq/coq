(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Normalisation functions for rational numbers. *)

Require Export QArith_base.
Require Import Znumtheory.

Notation Z2P := Z.to_pos (compat "8.3").
Notation Z2P_correct := Z2Pos.id (compat "8.3").

(** Simplification of fractions using [Z.gcd].
  This version can compute within Coq. *)

Definition Qred (q:Q) :=
  let (q1,q2) := q in
  let (r1,r2) := snd (Z.ggcd q1 ('q2))
  in r1#(Z.to_pos r2).

Lemma Qred_correct : forall q, (Qred q) == q.
Proof.
  unfold Qred, Qeq; intros (n,d); simpl.
  generalize (Z.ggcd_gcd n ('d)) (Z.gcd_nonneg n ('d))
    (Z.ggcd_correct_divisors n ('d)).
  destruct (Z.ggcd n (Zpos d)) as (g,(nn,dd)); simpl.
  Open Scope Z_scope.
  intros Hg LE (Hn,Hd). rewrite Hd, Hn.
  rewrite <- Hg in LE; clear Hg.
  assert (0 <> g) by (intro; subst; discriminate).
  rewrite Z2Pos.id. ring.
  rewrite <- (Z.mul_pos_cancel_l g); [now rewrite <- Hd | omega].
  Close Scope Z_scope.
Qed.

Lemma Qred_complete : forall p q,  p==q -> Qred p = Qred q.
Proof.
  intros (a,b) (c,d).
  unfold Qred, Qeq in *; simpl in *.
  Open Scope Z_scope.
  intros H.
  generalize (Z.ggcd_gcd a ('b)) (Zgcd_is_gcd a ('b))
    (Z.gcd_nonneg a ('b)) (Z.ggcd_correct_divisors a ('b)).
  destruct (Z.ggcd a (Zpos b)) as (g,(aa,bb)).
  simpl. intros <- Hg1 Hg2 (Hg3,Hg4).
  assert (Hg0 : g <> 0) by (intro; now subst g).
  generalize (Z.ggcd_gcd c ('d)) (Zgcd_is_gcd c ('d))
    (Z.gcd_nonneg c ('d)) (Z.ggcd_correct_divisors c ('d)).
  destruct (Z.ggcd c (Zpos d)) as (g',(cc,dd)).
  simpl. intros <- Hg'1 Hg'2 (Hg'3,Hg'4).
  assert (Hg'0 : g' <> 0) by (intro; now subst g').

  elim (rel_prime_cross_prod aa bb cc dd).
  - congruence.
  - (*rel_prime*)
    constructor.
    * exists aa; auto with zarith.
    * exists bb; auto with zarith.
    * intros x Ha Hb.
      destruct Hg1 as (Hg11,Hg12,Hg13).
      destruct (Hg13 (g*x)) as (x',Hx).
      { rewrite Hg3.
        destruct Ha as (xa,Hxa); exists xa; rewrite Hxa; ring. }
      { rewrite Hg4.
        destruct Hb as (xb,Hxb); exists xb; rewrite Hxb; ring. }
      exists x'.
      apply Z.mul_reg_l with g; auto. rewrite Hx at 1; ring.
  - (* rel_prime *)
    constructor.
    * exists cc; auto with zarith.
    * exists dd; auto with zarith.
    * intros x Hc Hd.
      inversion Hg'1 as (Hg'11,Hg'12,Hg'13).
      destruct (Hg'13 (g'*x)) as (x',Hx).
      { rewrite Hg'3.
        destruct Hc as (xc,Hxc); exists xc; rewrite Hxc; ring. }
      { rewrite Hg'4.
        destruct Hd as (xd,Hxd); exists xd; rewrite Hxd; ring. }
      exists x'.
      apply Z.mul_reg_l with g'; auto. rewrite Hx at 1; ring.
  - apply Z.lt_gt.
    rewrite <- (Z.mul_pos_cancel_l g); [now rewrite <- Hg4 | omega].
  - apply Z.lt_gt.
    rewrite <- (Z.mul_pos_cancel_l g'); [now rewrite <- Hg'4 | omega].
  - apply Z.mul_reg_l with (g*g').
    * rewrite Z.mul_eq_0. now destruct 1.
    * rewrite Z.mul_shuffle1, <- Hg3, <- Hg'4.
      now rewrite Z.mul_shuffle1, <- Hg'3, <- Hg4, H, Z.mul_comm.
  Close Scope Z_scope.
Qed.

Add Morphism Qred : Qred_comp.
Proof.
  intros q q' H.
  rewrite (Qred_correct q); auto.
  rewrite (Qred_correct q'); auto.
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

Add Morphism Qplus' : Qplus'_comp.
Proof.
  intros; unfold Qplus'.
  rewrite H, H0; auto with qarith.
Qed.

Add Morphism Qmult' : Qmult'_comp.
Proof.
  intros; unfold Qmult'.
  rewrite H, H0; auto with qarith.
Qed.

Add Morphism Qminus' : Qminus'_comp.
Proof.
  intros; unfold Qminus'.
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
