(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Normalisation functions for rational numbers. *)

Require Export QArith_base.
Require Import Znumtheory.

(** First, a function that (tries to) build a positive back from a Z. *)

Definition Z2P (z : Z) :=
  match z with
  | Z0 => 1%positive
  | Zpos p => p
  | Zneg p => p
  end.

Lemma Z2P_correct : forall z : Z, (0 < z)%Z -> Zpos (Z2P z) = z.
Proof.
 simple destruct z; simpl in |- *; auto; intros; discriminate.
Qed.

Lemma Z2P_correct2 : forall z : Z, 0%Z <> z -> Zpos (Z2P z) = Zabs z.
Proof.
 simple destruct z; simpl in |- *; auto; intros; elim H; auto.
Qed.

(** Simplification of fractions using [Zgcd].
  This version can compute within Coq. *)

Definition Qred (q:Q) := 
  let (q1,q2) := q in 
  let (r1,r2) := snd (Zggcd q1 ('q2)) 
  in r1#(Z2P r2).

Lemma Qred_correct : forall q, (Qred q) == q.
Proof.
  unfold Qred, Qeq; intros (n,d); simpl.
  generalize (Zggcd_gcd n ('d)) (Zgcd_is_pos n ('d)) 
    (Zgcd_is_gcd n ('d)) (Zggcd_correct_divisors n ('d)).
  destruct (Zggcd n (Zpos d)) as (g,(nn,dd)); simpl.
  Open Scope Z_scope.
  intuition.
  rewrite <- H in H0,H1; clear H.
  rewrite H5; rewrite H6.
  assert (0 <> g).
  intro; subst g; discriminate.
  
  assert (0 < dd).
  apply Zmult_gt_0_lt_0_reg_r with g.
  omega.
  rewrite Zmult_comm.
  rewrite <- H6; compute; auto.
  rewrite Z2P_correct; auto.
  ring.
  Close Scope Z_scope.
Qed.

Lemma Qred_complete : forall p q,  p==q -> Qred p = Qred q.
Proof.
  intros (a,b) (c,d).
  unfold Qred, Qeq in *; simpl in *.
  Open Scope Z_scope.
  generalize (Zggcd_gcd a ('b)) (Zgcd_is_gcd a ('b)) 
    (Zgcd_is_pos a ('b)) (Zggcd_correct_divisors a ('b)).
  destruct (Zggcd a (Zpos b)) as (g,(aa,bb)).
  generalize (Zggcd_gcd c ('d)) (Zgcd_is_gcd c ('d)) 
    (Zgcd_is_pos c ('d)) (Zggcd_correct_divisors c ('d)).
  destruct (Zggcd c (Zpos d)) as (g',(cc,dd)).
  simpl.
  intro H; rewrite <- H; clear H.
  intros Hg'1 Hg'2 (Hg'3,Hg'4).
  intro H; rewrite <- H; clear H.
  intros Hg1 Hg2 (Hg3,Hg4).
  intros.
  assert (g <> 0).
  intro; subst g; discriminate.
  assert (g' <> 0).
  intro; subst g'; discriminate.
  elim (rel_prime_cross_prod aa bb cc dd).
  congruence.
  unfold rel_prime in |- *.
  (*rel_prime*)
  constructor.
  exists aa; auto with zarith.
  exists bb; auto with zarith.
  intros.
  inversion Hg1.
  destruct (H6 (g*x)).
  rewrite Hg3.
  destruct H2 as (xa,Hxa); exists xa; rewrite Hxa; ring.
  rewrite Hg4.
  destruct H3 as (xb,Hxb); exists xb; rewrite Hxb; ring.
  exists q.
  apply Zmult_reg_l with g; auto.
  pattern g at 1; rewrite H7; ring.
  (* /rel_prime *)
  unfold rel_prime in |- *.
  (* rel_prime *)
  constructor.
  exists cc; auto with zarith.
  exists dd; auto with zarith.
  intros.
  inversion Hg'1.
  destruct (H6 (g'*x)).
  rewrite Hg'3.
  destruct H2 as (xc,Hxc); exists xc; rewrite Hxc; ring.
  rewrite Hg'4.
  destruct H3 as (xd,Hxd); exists xd; rewrite Hxd; ring.
  exists q.
  apply Zmult_reg_l with g'; auto.
  pattern g' at 1; rewrite H7; ring.
    (* /rel_prime *)
  assert (0<bb); [|auto with zarith].
  apply Zmult_gt_0_lt_0_reg_r with g.
  omega.
  rewrite Zmult_comm.
  rewrite <- Hg4; compute; auto.
  assert (0<dd); [|auto with zarith].
  apply Zmult_gt_0_lt_0_reg_r with g'.
  omega.
  rewrite Zmult_comm.
  rewrite <- Hg'4; compute; auto.
  apply Zmult_reg_l with (g'*g).
  intro H2; elim (Zmult_integral _ _ H2); auto.
  replace (g'*g*(aa*dd)) with ((g*aa)*(g'*dd)); [|ring].
  replace (g'*g*(bb*cc)) with ((g'*cc)*(g*bb)); [|ring].
  rewrite <- Hg3; rewrite <- Hg4; rewrite <- Hg'3; rewrite <- Hg'4; auto.
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
  intros; unfold Qplus' in |- *; apply Qred_correct; auto.
Qed.

Lemma Qmult'_correct : forall p q : Q, (Qmult' p q)==(Qmult p q).
Proof.
  intros; unfold Qmult' in |- *; apply Qred_correct; auto.
Qed.

Lemma Qminus'_correct : forall p q : Q, (Qminus' p q)==(Qminus p q).
Proof.
  intros; unfold Qminus' in |- *; apply Qred_correct; auto.
Qed.

Add Morphism Qplus' : Qplus'_comp.
Proof.
  intros; unfold Qplus' in |- *.
  rewrite H; rewrite H0; auto with qarith.
Qed.

Add Morphism Qmult' : Qmult'_comp.
  intros; unfold Qmult' in |- *.
  rewrite H; rewrite H0; auto with qarith.
Qed.

Add Morphism Qminus' : Qminus'_comp.
  intros; unfold Qminus' in |- *.
  rewrite H; rewrite H0; auto with qarith.
Qed.

Lemma Qred_opp: forall q, Qred (-q) = - (Qred q).
Proof.
  intros (x, y); unfold Qred; simpl.
  rewrite Zggcd_opp; case Zggcd; intros p1 (p2, p3); simpl.
  unfold Qopp; auto.
Qed.

Theorem Qred_compare: forall x y,
  Qcompare x y = Qcompare (Qred x) (Qred y).
Proof.
  intros x y; apply Qcompare_comp; apply Qeq_sym; apply Qred_correct.
Qed.

