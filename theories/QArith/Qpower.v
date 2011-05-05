(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Zpow_facts Qfield Qreduction.

Lemma Qpower_positive_1 : forall n, Qpower_positive 1 n == 1.
Proof.
induction n;
simpl; try rewrite IHn; reflexivity.
Qed.

Lemma Qpower_1 : forall n, 1^n == 1.
Proof.
  intros [|n|n]; simpl; try rewrite Qpower_positive_1; reflexivity.
Qed.

Lemma Qpower_positive_0 : forall n, Qpower_positive 0 n == 0.
Proof.
induction n;
simpl; try rewrite IHn; reflexivity.
Qed.

Lemma Qpower_0 : forall n, (n<>0)%Z -> 0^n == 0.
Proof.
  intros [|n|n] Hn; try (elim Hn; reflexivity); simpl;
  rewrite Qpower_positive_0; reflexivity.
Qed.

Lemma Qpower_not_0_positive : forall a n, ~a==0 -> ~Qpower_positive a n == 0.
Proof.
intros a n X H.
apply X; clear X.
induction n; simpl in *; try assumption;
destruct (Qmult_integral _ _ H);
try destruct (Qmult_integral _ _ H0); auto.
Qed.

Lemma Qpower_pos_positive : forall p n, 0 <= p -> 0 <= Qpower_positive p n.
intros p n Hp.
induction n; simpl; repeat apply Qmult_le_0_compat;assumption.
Qed.

Lemma Qpower_pos : forall p n, 0 <= p -> 0 <= p^n.
Proof.
  intros p [|n|n] Hp; simpl; try discriminate;
  try apply Qinv_le_0_compat;  apply Qpower_pos_positive; assumption.
Qed.

Lemma Qmult_power_positive  : forall a b n, Qpower_positive (a*b) n == (Qpower_positive a n)*(Qpower_positive b n).
Proof.
induction n;
simpl; repeat rewrite IHn; ring.
Qed.

Lemma Qmult_power : forall a b n, (a*b)^n == a^n*b^n.
Proof.
  intros a b [|n|n]; simpl;
  try rewrite Qmult_power_positive;
  try rewrite Qinv_mult_distr;
  reflexivity.
Qed.

Lemma Qinv_power_positive  : forall a n, Qpower_positive (/a) n == /(Qpower_positive a n).
Proof.
induction n;
simpl; repeat (rewrite IHn || rewrite Qinv_mult_distr); reflexivity.
Qed.

Lemma Qinv_power : forall a n, (/a)^n == /a^n.
Proof.
  intros a [|n|n]; simpl;
  try rewrite Qinv_power_positive;
  reflexivity.
Qed.

Lemma Qdiv_power : forall a b n, (a/b)^n == (a^n/b^n).
Proof.
unfold Qdiv.
intros a b n.
rewrite Qmult_power.
rewrite Qinv_power.
reflexivity.
Qed.

Lemma Qinv_power_n : forall n p, (1#p)^n == /(inject_Z ('p))^n.
Proof.
intros n p.
rewrite Qmake_Qdiv.
rewrite Qdiv_power.
rewrite Qpower_1.
unfold Qdiv.
ring.
Qed.

Lemma Qpower_plus_positive : forall a n m, Qpower_positive a (n+m) == (Qpower_positive a n)*(Qpower_positive a m).
Proof.
intros a n m.
unfold Qpower_positive.
apply pow_pos_Pplus.
apply Q_Setoid.
apply Qmult_comp.
apply Qmult_comm.
apply Qmult_assoc.
Qed.

Lemma Qpower_opp : forall a n, a^(-n) == /a^n.
Proof.
intros a [|n|n]; simpl; try reflexivity.
symmetry; apply Qinv_involutive.
Qed.

Lemma Qpower_minus_positive : forall a (n m:positive), (Pcompare n m Eq=Gt)%positive -> Qpower_positive a (n-m)%positive == (Qpower_positive a n)/(Qpower_positive a m).
Proof.
intros a n m H.
destruct (Qeq_dec a 0).
 rewrite q.
 repeat rewrite Qpower_positive_0.
 reflexivity.
rewrite <- (Qdiv_mult_l (Qpower_positive a (n - m)) (Qpower_positive a m)) by
 (apply Qpower_not_0_positive; assumption).
apply Qdiv_comp;[|reflexivity].
rewrite Qmult_comm.
rewrite <- Qpower_plus_positive.
rewrite Pplus_minus.
reflexivity.
assumption.
Qed.

Lemma Qpower_plus : forall a n m, ~a==0 -> a^(n+m) == a^n*a^m.
Proof.
intros a [|n|n] [|m|m] H; simpl; try ring;
try rewrite Qpower_plus_positive;
try apply Qinv_mult_distr; try reflexivity;
case_eq ((n ?= m)%positive); intros H0; simpl;
 try rewrite Qpower_minus_positive;
 try rewrite (Pcompare_Eq_eq _ _ H0);
 try (field; try split; apply Qpower_not_0_positive);
 try assumption;
 apply ZC2;
 assumption.
Qed.

Lemma Qpower_plus' : forall a n m, (n+m <> 0)%Z -> a^(n+m) == a^n*a^m.
Proof.
intros a n m H.
destruct (Qeq_dec a 0)as [X|X].
rewrite X.
rewrite Qpower_0 by assumption.
destruct n; destruct m; try (elim H; reflexivity);
 simpl; repeat rewrite Qpower_positive_0; ring_simplify;
 reflexivity.
apply Qpower_plus.
assumption.
Qed.

Lemma Qpower_mult_positive : forall a n m, Qpower_positive a (n*m) == Qpower_positive (Qpower_positive a n) m.
Proof.
intros a n m.
induction n using Pind.
 reflexivity.
rewrite Pmult_Sn_m.
rewrite Pplus_one_succ_l.
do 2 rewrite Qpower_plus_positive.
rewrite IHn.
rewrite Qmult_power_positive.
reflexivity.
Qed.

Lemma Qpower_mult : forall a n m, a^(n*m) ==  (a^n)^m.
Proof.
intros a [|n|n] [|m|m]; simpl;
 try rewrite Qpower_positive_1;
 try rewrite Qpower_mult_positive;
 try rewrite Qinv_power_positive;
 try rewrite Qinv_involutive;
 try reflexivity.
Qed.

Lemma Zpower_Qpower : forall (a n:Z), (0<=n)%Z -> inject_Z (a^n) == (inject_Z a)^n.
Proof.
intros a [|n|n] H;[reflexivity| |elim H; reflexivity].
induction n using Pind.
 replace (a^1)%Z with a by ring.
 ring.
rewrite Zpos_succ_morphism.
unfold Zsucc.
rewrite Zpower_exp; auto with *; try discriminate.
rewrite Qpower_plus' by discriminate.
rewrite <- IHn by discriminate.
replace (a^'n*a^1)%Z with (a^'n*a)%Z by ring.
ring_simplify.
reflexivity.
Qed.

Lemma Qsqr_nonneg : forall a, 0 <= a^2.
Proof.
intros a.
destruct (Qlt_le_dec 0 a) as [A|A].
apply (Qmult_le_0_compat a a);
 (apply Qlt_le_weak; assumption).
setoid_replace (a^2) with ((-a)*(-a)) by ring.
rewrite Qle_minus_iff in A.
setoid_replace (0+ - a) with (-a) in A by ring.
apply Qmult_le_0_compat; assumption.
Qed.

Theorem Qpower_decomp: forall p x y,
  Qpower_positive (x #y) p == x ^ Zpos p # (Z2P ((Zpos y) ^ Zpos p)).
Proof.
induction p; intros; unfold Qmult; simpl.
(* xI *)
rewrite IHp, xI_succ_xO, <-Pplus_diag, Pplus_one_succ_l.
repeat rewrite Zpower_pos_is_exp.
red; unfold Qmult, Qnum, Qden, Zpower.
repeat rewrite Zpos_mult_morphism.
repeat rewrite Z2P_correct.
repeat rewrite Zpower_pos_1_r; ring.
apply Zpower_pos_pos; red; auto.
repeat apply Zmult_lt_0_compat; red; auto;
 apply Zpower_pos_pos; red; auto.
(* xO *)
rewrite IHp, <-Pplus_diag.
repeat rewrite Zpower_pos_is_exp.
red; unfold Qmult, Qnum, Qden, Zpower.
repeat rewrite Zpos_mult_morphism.
repeat rewrite Z2P_correct; try ring.
apply Zpower_pos_pos; red; auto.
repeat apply Zmult_lt_0_compat; auto;
 apply Zpower_pos_pos; red; auto.
(* xO *)
unfold Qmult; simpl.
red; simpl; rewrite Zpower_pos_1_r;
 rewrite Zpos_mult_morphism; ring.
Qed.
