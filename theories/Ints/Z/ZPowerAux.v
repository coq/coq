
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

(**********************************************************************


    ZPowerAux.v      Auxillary functions & Theorems for Zpower 
 **********************************************************************)

Require Export ZArith.
Require Export Znumtheory.
Require Export Tactic.

Open Local Scope Z_scope. 

Hint  Extern 2 (Zle _ _) => 
 (match goal with
   |- Zpos _ <= Zpos _ => exact (refl_equal _)
|   H: _ <=  ?p |- _ <= ?p => apply Zle_trans with (2 := H)
|   H: _ <  ?p |- _ <= ?p => apply Zlt_le_weak; apply Zle_lt_trans with (2 := H)
  end).

Hint  Extern 2 (Zlt _ _) => 
 (match goal with
   |- Zpos _ < Zpos _ => exact (refl_equal _)
|      H: _ <=  ?p |- _ <= ?p => apply Zlt_le_trans with (2 := H)
|   H: _ <  ?p |- _ <= ?p => apply Zle_lt_trans with (2 := H)
  end).

Hint Resolve Zlt_gt Zle_ge: zarith.

(**************************************
  Properties Zpower
**************************************)

Theorem Zpower_1: forall a, 0 <= a ->  1 ^ a = 1.
intros a Ha; pattern a; apply natlike_ind; auto with zarith.
intros x Hx Hx1; unfold Zsucc.
rewrite Zpower_exp; auto with zarith.
rewrite Hx1; simpl; auto.
Qed.

Theorem Zpower_exp_0: forall a,  a ^ 0 = 1.
simpl; unfold Zpower_pos; simpl; auto with zarith.
Qed.

Theorem Zpower_exp_1: forall a,  a ^ 1 = a.
simpl; unfold Zpower_pos; simpl; auto with zarith.
Qed.

Theorem Zpower_Zabs: forall a b,  Zabs (a ^ b) = (Zabs a) ^ b.
intros a b; case (Zle_or_lt 0 b).
intros Hb; pattern b; apply natlike_ind; auto with zarith.
intros x Hx Hx1; unfold Zsucc.
(repeat rewrite Zpower_exp); auto with zarith.
rewrite Zabs_Zmult; rewrite Hx1.
eq_tac; auto.
replace (a ^ 1) with a; auto.
simpl; unfold Zpower_pos; simpl; rewrite Zmult_1_r; auto.
simpl; unfold Zpower_pos; simpl; rewrite Zmult_1_r; auto.
case b; simpl; auto with zarith.
intros p Hp; discriminate.
Qed.

Theorem Zpower_Zsucc: forall p n,  0 <= n -> p ^Zsucc n = p * p ^ n.
intros p n H.
unfold Zsucc; rewrite Zpower_exp; auto with zarith.
rewrite Zpower_exp_1; apply Zmult_comm.
Qed.

Theorem Zpower_mult: forall p q r,  0 <= q -> 0 <=  r -> p ^ (q * r) = (p ^ q) ^
 r.
intros p q r H1 H2; generalize H2; pattern r; apply natlike_ind; auto.
intros H3; rewrite Zmult_0_r; repeat rewrite Zpower_exp_0; auto.
intros r1 H3 H4 H5.
unfold Zsucc; rewrite Zpower_exp; auto with zarith.
rewrite <- H4; try rewrite Zpower_exp_1; try rewrite <- Zpower_exp; try eq_tac;
auto with zarith.
ring.
Qed.

Theorem Zpower_lt_0: forall a b: Z, 0 < a -> 0 <= b-> 0 < a ^b.
intros a b; case b; auto with zarith.
simpl; intros; auto with zarith.
2: intros p H H1; case H1; auto.
intros p H1 H; generalize H; pattern (Zpos p); apply natlike_ind; auto.
intros; case a; compute; auto.
intros p1 H2 H3 _; unfold Zsucc; rewrite Zpower_exp; simpl; auto with zarith.
apply Zmult_lt_O_compat; auto with zarith.
generalize H1; case a; compute; intros; auto; discriminate.
Qed.

Theorem Zpower_le_monotone: forall a b c: Z, 0 < a -> 0 <= b <= c -> a ^ b <= a ^ c.
intros a b c H (H1, H2).
rewrite <- (Zmult_1_r (a ^ b)); replace c with (b + (c - b)); auto with zarith.
rewrite Zpower_exp; auto with zarith.
apply Zmult_le_compat_l; auto with zarith.
assert (0 < a ^ (c - b)); auto with zarith.
apply Zpower_lt_0; auto with zarith.
apply Zlt_le_weak; apply Zpower_lt_0; auto with zarith.
Qed.


Theorem Zpower_le_0: forall a b: Z, 0 <= a -> 0 <= a ^b. 
intros a b; case b; auto with zarith.
simpl; auto with zarith.
intros p H1; assert (H: 0 <= Zpos p); auto with zarith.
generalize H; pattern (Zpos p); apply natlike_ind; auto.
intros p1 H2 H3 _; unfold Zsucc; rewrite Zpower_exp; simpl; auto with zarith.
apply Zmult_le_0_compat; auto with zarith.
generalize H1; case a; compute; intros; auto; discriminate.
Qed.

Hint Resolve Zpower_le_0 Zpower_lt_0: zarith.

Theorem Zpower_prod: forall p q r,  0 <= q -> 0 <=  r -> (p * q) ^ r = p ^ r * q ^ r.
intros p q r H1 H2; generalize H2; pattern r; apply natlike_ind; auto.
intros r1 H3 H4 H5.
unfold Zsucc; rewrite Zpower_exp; auto with zarith.
rewrite  H4;  repeat (rewrite Zpower_exp_1 || rewrite Zpower_exp); auto with zarith; ring.
Qed.

Theorem Zpower_le_monotone_exp: forall a b c: Z, 0 <= c -> 0 <= a <= b -> a ^ c <=  b ^ c.
intros a b c H (H1, H2).
generalize H; pattern c; apply natlike_ind; auto.
intros x HH HH1 _; unfold Zsucc; repeat rewrite Zpower_exp; auto with zarith.
repeat rewrite Zpower_exp_1.
apply Zle_trans with (a ^x * b); auto with zarith.
Qed.

Theorem Zpower_lt_monotone: forall a b c: Z, 1 < a -> 0 <= b < c -> a ^ b < a ^
 c.
intros a b c H (H1, H2).
rewrite <- (Zmult_1_r (a ^ b)); replace c with (b + (c - b)); auto with zarith.
rewrite Zpower_exp; auto with zarith.
apply Zmult_lt_compat_l; auto with zarith.
assert (0 < a ^ (c - b)); auto with zarith.
apply Zlt_le_trans with (a ^1); auto with zarith.
rewrite Zpower_exp_1; auto with zarith.
apply Zpower_le_monotone; auto with zarith.
Qed.

Lemma Zpower_le_monotone_inv  : 
  forall a b c, 1 < a -> 0 < b -> a^b <= a^c -> b <= c.
Proof.
 intros a b c H H0 H1.
 destruct (Z_le_gt_dec b c);trivial.
 assert (2 <= a^b).
  apply Zle_trans with (2^b).
  pattern 2 at 1;replace 2 with (2^1);trivial.
  apply Zpower_le_monotone;auto with zarith.
  apply Zpower_le_monotone_exp;auto with zarith.
 assert (c > 0).
 destruct (Z_le_gt_dec 0 c);trivial. 
 destruct (Zle_lt_or_eq _ _ z0);auto with zarith.
 rewrite <- H3 in H1;simpl in H1; elimtype False;omega.
 destruct c;try discriminate z0. simpl in H1. elimtype False;omega.
 assert (H4 := Zpower_lt_monotone a c b H). elimtype False;omega.
Qed.


Theorem Zpower_le_monotone2:
   forall a b c: Z, 0 < a -> b <= c -> a ^ b <= a ^ c.
intros a b c H H2.
destruct (Z_le_gt_dec 0 b).
rewrite <- (Zmult_1_r (a ^ b)); replace c with (b + (c - b)); auto with zarith.
rewrite Zpower_exp; auto with zarith.
apply Zmult_le_compat_l; auto with zarith.
assert (0 < a ^ (c - b)); auto with zarith.
replace (a^b) with 0.
destruct (Z_le_gt_dec 0 c).
destruct (Zle_lt_or_eq _ _ z0).
apply Zlt_le_weak;apply Zpower_lt_0;trivial.
rewrite <- H0;simpl;auto with zarith.
replace (a^c) with 0. auto with zarith.
destruct c;trivial;unfold Zgt in z0;discriminate z0.
destruct b;trivial;unfold Zgt in z;discriminate z.
Qed.

Theorem Zpower2_lt_lin: forall n,
  0 <= n -> n < 2 ^ n.
intros n; apply (natlike_ind (fun n => n < 2 ^n)); clear n.
 simpl; auto with zarith.
intros n H1 H2; unfold Zsucc.
case (Zle_lt_or_eq _ _ H1); clear H1; intros H1.
  apply Zle_lt_trans with (n + n); auto with zarith.
  rewrite Zpower_exp; auto with zarith.
  rewrite Zpower_exp_1.
  assert (tmp: forall p, p * 2 = p + p); intros; try ring;
  rewrite tmp; auto with zarith.
subst n; simpl; unfold Zpower_pos; simpl; auto with zarith.
Qed.

Theorem Zpower2_le_lin: forall n,
  0 <= n -> n <= 2 ^ n.
intros; apply Zlt_le_weak.
apply Zpower2_lt_lin; auto.
Qed.
