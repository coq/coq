(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import QArith.

Lemma Qopp_lt_compat: forall p q : Q, p < q -> - q < - p.
Proof.
intros (a1,a2) (b1,b2); unfold Qle, Qlt; simpl.
rewrite !Z.mul_opp_l; omega.
Qed.

Hint Resolve Qopp_lt_compat : qarith.

(************)

Local Coercion inject_Z : Z >-> Q.

Definition Qfloor (x:Q) := let (n,d) := x in Z.div n (Zpos d).
Definition Qceiling (x:Q) := (-(Qfloor (-x)))%Z.

Lemma Qfloor_Z : forall z:Z, Qfloor z = z.
Proof.
intros z.
simpl.
auto with *.
Qed.

Lemma Qceiling_Z : forall z:Z, Qceiling z = z.
Proof.
intros z.
unfold Qceiling.
simpl.
rewrite Zdiv_1_r.
auto with *.
Qed.

Lemma Qfloor_le : forall x, Qfloor x <= x.
Proof.
intros [n d].
simpl.
unfold Qle.
simpl.
replace (n*1)%Z with n by ring.
rewrite Z.mul_comm.
apply Z_mult_div_ge.
auto with *.
Qed.

Hint Resolve Qfloor_le : qarith.

Lemma Qle_ceiling : forall x, x <= Qceiling x.
Proof.
intros x.
apply Qle_trans with (- - x).
 rewrite Qopp_involutive.
 auto with *.
change (Qceiling x:Q) with (-(Qfloor(-x))).
auto with *.
Qed.

Hint Resolve Qle_ceiling : qarith.

Lemma Qle_floor_ceiling : forall x, Qfloor x <= Qceiling x.
Proof.
eauto with qarith.
Qed.

Lemma Qlt_floor : forall x, x < (Qfloor x+1)%Z.
Proof.
intros [n d].
simpl.
unfold Qlt.
simpl.
replace (n*1)%Z with n by ring.
ring_simplify.
replace (n / Zpos d * Zpos d + Zpos d)%Z with
  ((Zpos d * (n / Zpos d) + n mod Zpos  d) + Zpos  d - n mod Zpos d)%Z by ring.
rewrite <- Z_div_mod_eq; auto with*.
rewrite <- Z.lt_add_lt_sub_r.
destruct (Z_mod_lt n (Zpos d)); auto with *.
Qed.

Hint Resolve Qlt_floor : qarith.

Lemma Qceiling_lt : forall x, (Qceiling x-1)%Z < x.
Proof.
intros x.
unfold Qceiling.
replace (- Qfloor (- x) - 1)%Z with (-(Qfloor (-x) + 1))%Z by ring.
change ((- (Qfloor (- x) + 1))%Z:Q) with (-(Qfloor (- x) + 1)%Z).
apply Qlt_le_trans with (- - x); auto with *.
rewrite Qopp_involutive.
auto with *.
Qed.

Hint Resolve Qceiling_lt : qarith.

Lemma Qfloor_resp_le : forall x y, x <= y -> (Qfloor x <= Qfloor y)%Z.
Proof.
intros [xn xd] [yn yd] Hxy.
unfold Qle in *.
simpl in *.
rewrite <- (Zdiv_mult_cancel_r xn (Zpos xd) (Zpos yd)); auto with *.
rewrite <- (Zdiv_mult_cancel_r yn (Zpos yd) (Zpos xd)); auto with *.
rewrite (Z.mul_comm (Zpos yd) (Zpos xd)).
apply Z_div_le; auto with *.
Qed.

Hint Resolve Qfloor_resp_le : qarith.

Lemma Qceiling_resp_le : forall x y, x <= y -> (Qceiling x <= Qceiling y)%Z.
Proof.
intros x y Hxy.
unfold Qceiling.
cut (Qfloor (-y) <= Qfloor (-x))%Z; auto with *.
Qed.

Hint Resolve Qceiling_resp_le : qarith.

Add Morphism Qfloor with signature Qeq ==> eq as Qfloor_comp.
Proof.
intros x y H.
apply Z.le_antisymm.
 auto with *.
symmetry in H; auto with *.
Qed.

Add Morphism Qceiling with signature Qeq ==> eq as Qceiling_comp.
Proof.
intros x y H.
apply Z.le_antisymm.
 auto with *.
symmetry in H; auto with *.
Qed.

Lemma Zdiv_Qdiv (n m: Z): (n / m)%Z = Qfloor (n / m).
Proof.
 unfold Qfloor. intros. simpl.
 destruct m as [ | | p]; simpl.
  now rewrite Zdiv_0_r, Z.mul_0_r.
  now rewrite Z.mul_1_r.
 rewrite <- Z.opp_eq_mul_m1.
 rewrite <- (Z.opp_involutive (Zpos p)).
 now rewrite Zdiv_opp_opp.
Qed.
