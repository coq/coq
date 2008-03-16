(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import QArith.

Lemma Qopp_lt_compat: forall p q : Q, p < q -> - q < - p.
Proof.
intros (a1,a2) (b1,b2); unfold Qle, Qlt; simpl.
do 2 rewrite <- Zopp_mult_distr_l; omega.
Qed.

Hint Resolve Qopp_lt_compat : qarith.

(************)

Coercion Local inject_Z : Z >-> Q.

Definition Qfloor (x:Q) := let (n,d) := x in Zdiv n (Zpos d).
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
rewrite Zmult_comm.
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
replace (n / ' d * ' d + ' d)%Z with
  (('d * (n / 'd) + n mod 'd) + 'd - n mod 'd)%Z by ring.
rewrite <- Z_div_mod_eq; auto with*.
rewrite <- Zlt_plus_swap.
destruct (Z_mod_lt n ('d)); auto with *.
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
rewrite <- (Zdiv_mult_cancel_r xn ('xd) ('yd)); auto with *.
rewrite <- (Zdiv_mult_cancel_r yn ('yd) ('xd)); auto with *.
rewrite (Zmult_comm ('yd) ('xd)).
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

Add Morphism Qfloor with signature Qeq ==> @eq _ as Qfloor_comp.
Proof.
intros x y H.
apply Zle_antisym.
 auto with *.
symmetry in H; auto with *.
Qed.

Add Morphism Qceiling with signature Qeq ==> @eq _ as Qceiling_comp.
Proof.
intros x y H.
apply Zle_antisym.
 auto with *.
symmetry in H; auto with *.
Qed.