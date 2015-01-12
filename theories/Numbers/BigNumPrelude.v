(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

(** * BigNumPrelude *)

(** Auxillary functions & theorems used for arbitrary precision efficient
    numbers. *)


Require Import ArithRing.
Require Export ZArith.
Require Export Znumtheory.
Require Export Zpow_facts.

Declare ML Module "numbers_syntax_plugin".

(* *** Nota Bene ***
   All results that were general enough has been moved in ZArith.
   Only remain here specialized lemmas and compatibility elements.
   (P.L. 5/11/2007).
*)


Local Open Scope Z_scope.

(* For compatibility of scripts, weaker version of some lemmas of Z.div *)

Lemma Zlt0_not_eq : forall n, 0<n -> n<>0.
Proof.
 auto with zarith.
Qed.

Definition Zdiv_mult_cancel_r a b c H := Zdiv.Zdiv_mult_cancel_r a b c (Zlt0_not_eq _ H).
Definition Zdiv_mult_cancel_l a b c H := Zdiv.Zdiv_mult_cancel_r a b c (Zlt0_not_eq _ H).
Definition Z_div_plus_l a b c H := Zdiv.Z_div_plus_full_l a b c (Zlt0_not_eq _ H).

(* Automation *)

Hint  Extern 2 (Z.le _ _) =>
 (match goal with
   |- Zpos _ <= Zpos _ => exact (eq_refl _)
|   H: _ <=  ?p |- _ <= ?p => apply Z.le_trans with (2 := H)
|   H: _ <  ?p |- _ <= ?p => apply Z.lt_le_incl; apply Z.le_lt_trans with (2 := H)
  end).

Hint  Extern 2 (Z.lt _ _) =>
 (match goal with
   |- Zpos _ < Zpos _ => exact (eq_refl _)
|      H: _ <=  ?p |- _ <= ?p => apply Z.lt_le_trans with (2 := H)
|   H: _ <  ?p |- _ <= ?p => apply Z.le_lt_trans with (2 := H)
  end).


Hint Resolve Z.lt_gt Z.le_ge Z_div_pos: zarith.

(**************************************
   Properties of order and product
 **************************************)

 Theorem beta_lex: forall a b c d beta,
       a * beta + b <= c * beta + d ->
       0 <= b < beta -> 0 <= d < beta ->
       a <= c.
 Proof.
  intros a b c d beta H1 (H3, H4) (H5, H6).
  assert (a - c < 1); auto with zarith.
  apply Z.mul_lt_mono_pos_r with beta; auto with zarith.
  apply Z.le_lt_trans with (d  - b); auto with zarith.
  rewrite Z.mul_sub_distr_r; auto with zarith.
 Qed.

 Theorem beta_lex_inv: forall a b c d beta,
      a < c -> 0 <= b < beta ->
      0 <= d < beta ->
      a * beta + b < c * beta  + d.
 Proof.
  intros a b c d beta H1 (H3, H4) (H5, H6).
  case (Z.le_gt_cases (c * beta + d) (a * beta + b)); auto with zarith.
  intros H7. contradict H1. apply Z.le_ngt. apply beta_lex with (1 := H7); auto.
 Qed.

 Lemma beta_mult : forall h l beta,
   0 <= h < beta -> 0 <= l < beta -> 0 <= h*beta+l < beta^2.
 Proof.
  intros h l beta H1 H2;split. auto with zarith.
  rewrite <- (Z.add_0_r (beta^2)); rewrite Z.pow_2_r;
   apply beta_lex_inv;auto with zarith.
 Qed.

 Lemma Zmult_lt_b :
   forall b x y, 0 <= x < b -> 0 <= y < b -> 0 <= x * y <= b^2 - 2*b + 1.
 Proof.
  intros b x y (Hx1,Hx2) (Hy1,Hy2);split;auto with zarith.
  apply Z.le_trans with ((b-1)*(b-1)).
  apply Z.mul_le_mono_nonneg;auto with zarith.
  apply Z.eq_le_incl; ring.
 Qed.

 Lemma sum_mul_carry : forall xh xl yh yl wc cc beta,
   1 < beta ->
   0 <= wc < beta ->
   0 <= xh < beta ->
   0 <= xl < beta ->
   0 <= yh < beta ->
   0 <= yl < beta ->
   0 <= cc < beta^2 ->
   wc*beta^2 + cc = xh*yl + xl*yh ->
   0 <= wc <= 1.
 Proof.
  intros xh xl yh yl wc cc beta U H1 H2 H3 H4 H5 H6 H7.
  assert (H8 := Zmult_lt_b beta xh yl H2 H5).
  assert (H9 := Zmult_lt_b beta xl yh H3 H4).
  split;auto with zarith.
  apply beta_lex with (cc) (beta^2 - 2) (beta^2); auto with zarith.
 Qed.

 Theorem mult_add_ineq: forall x y cross beta,
   0 <= x < beta ->
   0 <= y < beta ->
   0 <= cross < beta ->
   0 <= x * y + cross < beta^2.
 Proof.
  intros x y cross beta HH HH1 HH2.
  split; auto with zarith.
  apply Z.le_lt_trans with  ((beta-1)*(beta-1)+(beta-1)); auto with zarith.
  apply Z.add_le_mono; auto with zarith.
  apply Z.mul_le_mono_nonneg; auto with zarith.
  rewrite ?Z.mul_sub_distr_l, ?Z.mul_sub_distr_r, Z.pow_2_r; auto with zarith.
 Qed.

 Theorem mult_add_ineq2: forall x y c cross beta,
   0 <= x < beta ->
   0 <= y < beta ->
   0 <= c*beta + cross <= 2*beta - 2 ->
   0 <= x * y + (c*beta + cross) < beta^2.
 Proof.
  intros x y c cross beta HH HH1 HH2.
  split; auto with zarith.
  apply Z.le_lt_trans with ((beta-1)*(beta-1)+(2*beta-2));auto with zarith.
  apply Z.add_le_mono; auto with zarith.
  apply Z.mul_le_mono_nonneg; auto with zarith.
  rewrite ?Z.mul_sub_distr_l, ?Z.mul_sub_distr_r, Z.pow_2_r; auto with zarith.
 Qed.

Theorem mult_add_ineq3: forall x y c cross beta,
   0 <= x < beta ->
   0 <= y < beta ->
   0 <= cross <= beta - 2 ->
   0 <= c <= 1 ->
   0 <= x * y + (c*beta + cross) < beta^2.
 Proof.
  intros x y c cross beta HH HH1 HH2 HH3.
  apply mult_add_ineq2;auto with zarith.
  split;auto with zarith.
  apply Z.le_trans with (1*beta+cross);auto with zarith.
 Qed.

Hint Rewrite Z.mul_1_r Z.mul_0_r Z.mul_1_l Z.mul_0_l Z.add_0_l Z.add_0_r Z.sub_0_r: rm10.


(**************************************
 Properties of Z.div and Z.modulo
**************************************)

Theorem Zmod_le_first: forall a b, 0 <= a -> 0 < b -> 0 <= a mod b <= a.
 Proof.
  intros a b H H1;case (Z_mod_lt a b);auto with zarith;intros H2 H3;split;auto.
  case (Z.le_gt_cases b a); intros H4; auto with zarith.
  rewrite Zmod_small; auto with zarith.
 Qed.


 Theorem Zmod_distr: forall a b r t, 0 <= a <= b -> 0 <= r -> 0 <= t < 2 ^a ->
  (2 ^a * r + t) mod (2 ^ b) = (2 ^a * r) mod (2 ^ b) + t.
 Proof.
  intros a b r t (H1, H2) H3 (H4, H5).
  assert (t < 2 ^ b).
  apply Z.lt_le_trans with (1:= H5); auto with zarith.
  apply Zpower_le_monotone; auto with zarith.
  rewrite Zplus_mod; auto with zarith.
  rewrite Zmod_small with (a := t); auto with zarith.
  apply Zmod_small; auto with zarith.
  split; auto with zarith.
  assert (0 <= 2 ^a * r); auto with zarith.
  apply Z.add_nonneg_nonneg; auto with zarith.
  match goal with |- context [?X mod ?Y] => case (Z_mod_lt X Y) end;
   auto with zarith.
  pattern (2 ^ b) at 2; replace (2 ^ b) with ((2 ^ b - 2 ^a) + 2 ^ a);
    try ring.
  apply Z.add_le_lt_mono; auto with zarith.
  replace b with ((b - a) + a); try ring.
  rewrite Zpower_exp; auto with zarith.
  pattern (2 ^a) at 4; rewrite <- (Z.mul_1_l (2 ^a));
   try rewrite <- Z.mul_sub_distr_r.
  rewrite (Z.mul_comm (2 ^(b - a))); rewrite  Zmult_mod_distr_l;
   auto with zarith.
  rewrite (Z.mul_comm (2 ^a)); apply Z.mul_le_mono_nonneg_r; auto with zarith.
  match goal with |- context [?X mod ?Y] => case (Z_mod_lt X Y) end;
   auto with zarith.
 Qed.

 Theorem Zmod_shift_r:
   forall a b r t, 0 <= a <= b -> 0 <= r -> 0 <= t < 2 ^a ->
     (r * 2 ^a + t) mod (2 ^ b) = (r * 2 ^a) mod (2 ^ b) + t.
 Proof.
  intros a b r t (H1, H2) H3 (H4, H5).
  assert (t < 2 ^ b).
  apply Z.lt_le_trans with (1:= H5); auto with zarith.
  apply Zpower_le_monotone; auto with zarith.
  rewrite Zplus_mod; auto with zarith.
  rewrite Zmod_small with (a := t); auto with zarith.
  apply Zmod_small; auto with zarith.
  split; auto with zarith.
  assert (0 <= 2 ^a * r); auto with zarith.
  apply Z.add_nonneg_nonneg; auto with zarith.
  match goal with |- context [?X mod ?Y] => case (Z_mod_lt X Y) end;
   auto with zarith.
  pattern (2 ^ b) at 2;replace (2 ^ b) with ((2 ^ b - 2 ^a) + 2 ^ a); try ring.
  apply Z.add_le_lt_mono; auto with zarith.
  replace b with ((b - a) + a); try ring.
  rewrite Zpower_exp; auto with zarith.
  pattern (2 ^a) at 4; rewrite <- (Z.mul_1_l (2 ^a));
   try rewrite <- Z.mul_sub_distr_r.
  repeat rewrite (fun x => Z.mul_comm x (2 ^ a)); rewrite Zmult_mod_distr_l;
   auto with zarith.
  apply Z.mul_le_mono_nonneg_l; auto with zarith.
  match goal with |- context [?X mod ?Y] => case (Z_mod_lt X Y) end;
   auto with zarith.
 Qed.

  Theorem Zdiv_shift_r:
    forall a b r t, 0 <= a <= b -> 0 <= r -> 0 <= t < 2 ^a ->
      (r * 2 ^a + t) /  (2 ^ b) = (r * 2 ^a) / (2 ^ b).
  Proof.
   intros a b r t (H1, H2) H3 (H4, H5).
   assert (Eq: t < 2 ^ b); auto with zarith.
   apply Z.lt_le_trans with (1 := H5); auto with zarith.
   apply Zpower_le_monotone; auto with zarith.
   pattern (r * 2 ^ a) at 1; rewrite Z_div_mod_eq with (b := 2 ^ b);
    auto with zarith.
   rewrite <- Z.add_assoc.
   rewrite <- Zmod_shift_r; auto with zarith.
   rewrite (Z.mul_comm (2 ^ b)); rewrite Z_div_plus_full_l; auto with zarith.
   rewrite (fun x y => @Zdiv_small (x mod y)); auto with zarith.
   match goal with |- context [?X mod ?Y] => case (Z_mod_lt X Y) end;
    auto with zarith.
  Qed.


 Lemma shift_unshift_mod : forall n p a,
     0 <= a < 2^n ->
     0 <= p <= n ->
     a * 2^p = a / 2^(n - p) * 2^n + (a*2^p) mod 2^n.
 Proof.
  intros n p a H1 H2.
  pattern (a*2^p) at 1;replace (a*2^p) with
     (a*2^p/2^n * 2^n + a*2^p mod 2^n).
  2:symmetry;rewrite (Z.mul_comm (a*2^p/2^n));apply Z_div_mod_eq.
  replace (a * 2 ^ p / 2 ^ n) with (a / 2 ^ (n - p));trivial.
  replace (2^n) with (2^(n-p)*2^p).
  symmetry;apply Zdiv_mult_cancel_r.
  destruct H1;trivial.
  cut (0 < 2^p); auto with zarith.
  rewrite <- Zpower_exp.
  replace (n-p+p) with n;trivial. ring.
  omega. omega.
  apply Z.lt_gt. apply Z.pow_pos_nonneg;auto with zarith.
 Qed.


 Lemma shift_unshift_mod_2 : forall n p a, 0 <= p <= n ->
   ((a * 2 ^ (n - p)) mod (2^n) / 2 ^ (n - p)) mod (2^n) =
   a mod 2 ^ p.
 Proof.
 intros.
 rewrite Zmod_small.
 rewrite Zmod_eq by (auto with zarith).
 unfold Z.sub at 1.
 rewrite Z_div_plus_l by (auto with zarith).
 assert (2^n = 2^(n-p)*2^p).
  rewrite <- Zpower_exp by (auto with zarith).
  replace (n-p+p) with n; auto with zarith.
 rewrite H0.
 rewrite <- Zdiv_Zdiv, Z_div_mult by (auto with zarith).
 rewrite (Z.mul_comm (2^(n-p))), Z.mul_assoc.
 rewrite <- Z.mul_opp_l.
 rewrite Z_div_mult by (auto with zarith).
 symmetry; apply Zmod_eq; auto with zarith.

 remember (a * 2 ^ (n - p)) as b.
 destruct (Z_mod_lt b (2^n)); auto with zarith.
 split.
 apply Z_div_pos; auto with zarith.
 apply Zdiv_lt_upper_bound; auto with zarith.
 apply Z.lt_le_trans with (2^n); auto with zarith.
 rewrite <- (Z.mul_1_r (2^n)) at 1.
 apply Z.mul_le_mono_nonneg; auto with zarith.
 cut (0 < 2 ^ (n-p)); auto with zarith.
 Qed.

 Lemma div_le_0 : forall p x, 0 <= x -> 0 <= x / 2 ^ p.
 Proof.
  intros p x Hle;destruct (Z_le_gt_dec 0 p).
  apply  Zdiv_le_lower_bound;auto with zarith.
  replace (2^p) with 0.
  destruct x;compute;intro;discriminate.
  destruct p;trivial;discriminate.
 Qed.

 Lemma div_lt : forall p x y, 0 <= x < y -> x / 2^p < y.
 Proof.
  intros p x y H;destruct (Z_le_gt_dec 0 p).
  apply Zdiv_lt_upper_bound;auto with zarith.
  apply Z.lt_le_trans with y;auto with zarith.
  rewrite <- (Z.mul_1_r y);apply Z.mul_le_mono_nonneg;auto with zarith.
  assert (0 < 2^p);auto with zarith.
  replace (2^p) with 0.
  destruct x;change (0<y);auto with zarith.
  destruct p;trivial;discriminate.
 Qed.

 Theorem Zgcd_div_pos a b:
   0 < b -> 0 < Z.gcd a b -> 0 < b / Z.gcd a b.
 Proof.
 intros Hb Hg.
 assert (H : 0 <= b / Z.gcd a b) by (apply Z.div_pos; auto with zarith).
 Z.le_elim H; trivial.
 rewrite (Zdivide_Zdiv_eq (Z.gcd a b) b), <- H, Z.mul_0_r in Hb;
  auto using Z.gcd_divide_r with zarith.
 Qed.

 Theorem Zdiv_neg a b:
   a < 0 -> 0 < b -> a / b < 0.
 Proof.
 intros Ha Hb.
 assert (b > 0) by omega.
 generalize (Z_mult_div_ge a _ H); intros.
 assert (b * (a / b) < 0)%Z.
  apply Z.le_lt_trans with a; auto with zarith.
 destruct b; try (compute in Hb; discriminate).
 destruct (a/Zpos p)%Z.
 compute in H1; discriminate.
 compute in H1; discriminate.
 compute; auto.
 Qed.

 Lemma Zdiv_gcd_zero : forall a b, b / Z.gcd a b = 0 -> b <> 0 ->
  Z.gcd a b = 0.
 Proof.
 intros.
 generalize (Zgcd_is_gcd a b); destruct 1.
 destruct H2 as (k,Hk).
 generalize H; rewrite Hk at 1.
 destruct (Z.eq_dec (Z.gcd a b) 0) as [H'|H']; auto.
 rewrite Z_div_mult_full; auto.
 intros; subst k; simpl in *; subst b; elim H0; auto.
 Qed.

 Lemma Zgcd_mult_rel_prime : forall a b c,
  Z.gcd a c = 1 -> Z.gcd b c = 1 -> Z.gcd (a*b) c = 1.
 Proof.
 intros.
 rewrite Zgcd_1_rel_prime in *.
 apply rel_prime_sym; apply rel_prime_mult; apply rel_prime_sym; auto.
 Qed.

 Lemma Zcompare_gt : forall (A:Type)(a a':A)(p q:Z),
  match (p?=q)%Z with Gt => a | _ => a' end =
  if Z_le_gt_dec p q then a' else a.
 Proof.
 intros.
 destruct Z_le_gt_dec as [H|H].
 red in H.
 destruct (p?=q)%Z; auto; elim H; auto.
 rewrite H; auto.
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

Lemma Zsquare_le x : x <= x*x.
Proof.
destruct (Z.lt_ge_cases 0 x).
- rewrite <- Z.mul_1_l at 1.
  rewrite <- Z.mul_le_mono_pos_r; auto with zarith.
- pose proof (Z.square_nonneg x); auto with zarith.
Qed.
