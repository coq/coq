(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

(*i $Id$ i*)

(** * BigNumPrelude *)

(** Auxillary functions & theorems used for arbitrary precision efficient
    numbers. *)


Require Import ArithRing.
Require Export ZArith.
Require Export Znumtheory.
Require Export Zpow_facts.

(* *** Nota Bene ***
   All results that were general enough has been moved in ZArith.
   Only remain here specialized lemmas and compatibility elements.
   (P.L. 5/11/2007).
*)


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


Hint Resolve Zlt_gt Zle_ge Z_div_pos: zarith.

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
  apply Zmult_lt_reg_r with beta; auto with zarith.
  apply Zle_lt_trans with (d  - b); auto with zarith.
  rewrite Zmult_minus_distr_r; auto with zarith.
 Qed.

 Theorem beta_lex_inv: forall a b c d beta,
      a < c -> 0 <= b < beta ->
      0 <= d < beta -> 
      a * beta + b < c * beta  + d. 
 Proof.
  intros a b c d beta H1 (H3, H4) (H5, H6).
  case (Zle_or_lt (c * beta + d) (a * beta + b)); auto with zarith.
  intros H7; contradict H1;apply Zle_not_lt;apply beta_lex with (1 := H7);auto.
 Qed.

 Lemma beta_mult : forall h l beta, 
   0 <= h < beta -> 0 <= l < beta -> 0 <= h*beta+l < beta^2.
 Proof.
  intros h l beta H1 H2;split. auto with zarith.
  rewrite <- (Zplus_0_r (beta^2)); rewrite Zpower_2;
   apply beta_lex_inv;auto with zarith.
 Qed.

 Lemma Zmult_lt_b : 
   forall b x y, 0 <= x < b -> 0 <= y < b -> 0 <= x * y <= b^2 - 2*b + 1.
 Proof.
  intros b x y (Hx1,Hx2) (Hy1,Hy2);split;auto with zarith.
  apply Zle_trans with ((b-1)*(b-1)).
  apply Zmult_le_compat;auto with zarith.
  apply Zeq_le;ring.
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
  apply Zle_lt_trans with  ((beta-1)*(beta-1)+(beta-1)); auto with zarith.
  apply Zplus_le_compat; auto with zarith.
  apply Zmult_le_compat; auto with zarith.
  repeat (rewrite Zmult_minus_distr_l || rewrite Zmult_minus_distr_r); 
  rewrite Zpower_2; auto with zarith.
 Qed.

 Theorem mult_add_ineq2: forall x y c cross beta,
   0 <= x < beta ->
   0 <= y < beta ->
   0 <= c*beta + cross <= 2*beta - 2 ->
   0 <= x * y + (c*beta + cross) < beta^2.
 Proof.
  intros x y c cross beta HH HH1 HH2.
  split; auto with zarith.
  apply Zle_lt_trans with ((beta-1)*(beta-1)+(2*beta-2));auto with zarith.
  apply Zplus_le_compat; auto with zarith.
  apply Zmult_le_compat; auto with zarith.
  repeat (rewrite Zmult_minus_distr_l || rewrite Zmult_minus_distr_r); 
   rewrite Zpower_2; auto with zarith.
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
  apply Zle_trans with (1*beta+cross);auto with zarith.
 Qed.

Hint Rewrite Zmult_1_r Zmult_0_r Zmult_1_l Zmult_0_l Zplus_0_l Zplus_0_r Zminus_0_r: rm10.


(**************************************
 Properties of Zdiv and Zmod
**************************************)

Theorem Zmod_le_first: forall a b, 0 <= a -> 0 < b -> 0 <= a mod b <= a.
 Proof.
  intros a b H H1;case (Z_mod_lt a b);auto with zarith;intros H2 H3;split;auto.
  case (Zle_or_lt b a); intros H4; auto with zarith.
  rewrite Zmod_small; auto with zarith.
 Qed.


 Theorem Zmod_distr: forall a b r t, 0 <= a <= b -> 0 <= r -> 0 <= t < 2 ^a ->
  (2 ^a * r + t) mod (2 ^ b) = (2 ^a * r) mod (2 ^ b) + t.
 Proof.
  intros a b r t (H1, H2) H3 (H4, H5).
  assert (t < 2 ^ b).
  apply Zlt_le_trans with (1:= H5); auto with zarith.
  apply Zpower_le_monotone; auto with zarith.
  rewrite Zplus_mod; auto with zarith.
  rewrite Zmod_small with (a := t); auto with zarith.
  apply Zmod_small; auto with zarith.
  split; auto with zarith.
  assert (0 <= 2 ^a * r); auto with zarith.
  apply Zplus_le_0_compat; auto with zarith.
  match goal with |- context [?X mod ?Y] => case (Z_mod_lt X Y) end;
   auto with zarith.
  pattern (2 ^ b) at 2; replace (2 ^ b) with ((2 ^ b - 2 ^a) + 2 ^ a);
    try ring.
  apply Zplus_le_lt_compat; auto with zarith.
  replace b with ((b - a) + a); try ring.
  rewrite Zpower_exp; auto with zarith.
  pattern (2 ^a) at 4; rewrite <- (Zmult_1_l (2 ^a)); 
   try rewrite <- Zmult_minus_distr_r.
  rewrite (Zmult_comm (2 ^(b - a))); rewrite  Zmult_mod_distr_l; 
   auto with zarith.
  rewrite (Zmult_comm (2 ^a)); apply Zmult_le_compat_r; auto with zarith.
  match goal with |- context [?X mod ?Y] => case (Z_mod_lt X Y) end;
   auto with zarith.
 Qed.

 Theorem Zmod_shift_r:
   forall a b r t, 0 <= a <= b -> 0 <= r -> 0 <= t < 2 ^a ->
     (r * 2 ^a + t) mod (2 ^ b) = (r * 2 ^a) mod (2 ^ b) + t.
 Proof.
  intros a b r t (H1, H2) H3 (H4, H5).
  assert (t < 2 ^ b).
  apply Zlt_le_trans with (1:= H5); auto with zarith.
  apply Zpower_le_monotone; auto with zarith.
  rewrite Zplus_mod; auto with zarith.
  rewrite Zmod_small with (a := t); auto with zarith.
  apply Zmod_small; auto with zarith.
  split; auto with zarith.
  assert (0 <= 2 ^a * r); auto with zarith.
  apply Zplus_le_0_compat; auto with zarith.
  match goal with |- context [?X mod ?Y] => case (Z_mod_lt X Y) end; 
   auto with zarith.
  pattern (2 ^ b) at 2;replace (2 ^ b) with ((2 ^ b - 2 ^a) + 2 ^ a); try ring.
  apply Zplus_le_lt_compat; auto with zarith.
  replace b with ((b - a) + a); try ring.
  rewrite Zpower_exp; auto with zarith.
  pattern (2 ^a) at 4; rewrite <- (Zmult_1_l (2 ^a)); 
   try rewrite <- Zmult_minus_distr_r.
  repeat rewrite (fun x => Zmult_comm x (2 ^ a)); rewrite Zmult_mod_distr_l;
   auto with zarith.
  apply Zmult_le_compat_l; auto with zarith.
  match goal with |- context [?X mod ?Y] => case (Z_mod_lt X Y) end; 
   auto with zarith.
 Qed.

  Theorem Zdiv_shift_r: 
    forall a b r t, 0 <= a <= b -> 0 <= r -> 0 <= t < 2 ^a ->
      (r * 2 ^a + t) /  (2 ^ b) = (r * 2 ^a) / (2 ^ b).
  Proof.
   intros a b r t (H1, H2) H3 (H4, H5).
   assert (Eq: t < 2 ^ b); auto with zarith.
   apply Zlt_le_trans with (1 := H5); auto with zarith.
   apply Zpower_le_monotone; auto with zarith.
   pattern (r * 2 ^ a) at 1; rewrite Z_div_mod_eq with (b := 2 ^ b);
    auto with zarith.
   rewrite <- Zplus_assoc.
   rewrite <- Zmod_shift_r; auto with zarith.
   rewrite (Zmult_comm (2 ^ b)); rewrite Z_div_plus_full_l; auto with zarith.
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
  2:symmetry;rewrite (Zmult_comm (a*2^p/2^n));apply Z_div_mod_eq.
  replace (a * 2 ^ p / 2 ^ n) with (a / 2 ^ (n - p));trivial.
  replace (2^n) with (2^(n-p)*2^p).
  symmetry;apply Zdiv_mult_cancel_r.
  destruct H1;trivial.
  cut (0 < 2^p); auto with zarith.
  rewrite <- Zpower_exp.
  replace (n-p+p) with n;trivial. ring.
  omega. omega.
  apply Zlt_gt. apply Zpower_gt_0;auto with zarith.
 Qed.

 Lemma div_le_0 : forall p x, 0 <= x -> 0 <= x / 2 ^ p.
 Proof.
  intros p x Hle;destruct (Z_le_gt_dec 0 p).
  apply  Zdiv_le_lower_bound;auto with zarith. 
  replace (2^p) with 0.
  destruct x;compute;intro;discriminate.
  destruct p;trivial;discriminate z.
 Qed.
 
 Lemma div_lt : forall p x y, 0 <= x < y -> x / 2^p < y.
 Proof.
  intros p x y H;destruct (Z_le_gt_dec 0 p).
  apply Zdiv_lt_upper_bound;auto with zarith. 
  apply Zlt_le_trans with y;auto with zarith.
  rewrite <- (Zmult_1_r y);apply Zmult_le_compat;auto with zarith.
  assert (0 < 2^p);auto with zarith.
  replace (2^p) with 0.
  destruct x;change (0<y);auto with zarith.
  destruct p;trivial;discriminate z.
 Qed.

 Theorem Zgcd_div_pos a b:
   (0 < b)%Z -> (0 < Zgcd a b)%Z -> (0 < b / Zgcd a b)%Z.
 Proof.
 intros a b Ha Hg.
 case (Zle_lt_or_eq 0 (b/Zgcd a b)); auto.
 apply Z_div_pos; auto with zarith.
 intros H; generalize Ha.
 pattern b at 1; rewrite (Zdivide_Zdiv_eq (Zgcd a b) b); auto.
 rewrite <- H; auto with zarith.
 assert (F := (Zgcd_is_gcd a b)); inversion F; auto.
 Qed.
 
(* For compatibility of scripts, weaker version of some lemmas of Zdiv *)

Lemma Zlt0_not_eq : forall n, 0<n -> n<>0.
Proof.
 auto with zarith.
Qed.

Definition Zdiv_mult_cancel_r a b c H := Zdiv.Zdiv_mult_cancel_r a b c (Zlt0_not_eq _ H).
Definition Zdiv_mult_cancel_l a b c H := Zdiv.Zdiv_mult_cancel_r a b c (Zlt0_not_eq _ H).
Definition Z_div_plus_l a b c H := Zdiv.Z_div_plus_full_l a b c (Zlt0_not_eq _ H).

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
destruct (Zle_or_lt b 0) as [H | H]. now right. left; now split.
intros n H IH. destruct IH as [[IH1 IH2] | IH].
destruct (Zle_or_lt (b - 1) n) as [H1 | H1].
right; auto with zarith.
left. split; [auto with zarith | now apply (QS n)].
right; auto with zarith.
unfold Q' in *; intros n H1 H2. destruct (H n H1) as [[H3 H4] | H3].
assumption. apply Zle_not_lt in H3. false_hyp H2 H3.
Qed.
