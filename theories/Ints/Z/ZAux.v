
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

(**********************************************************************
     Aux.v

     Auxillary functions & Theorems
 **********************************************************************)

Require Import ArithRing.
Require Export ZArith.
Require Export Znumtheory.
Require Export Tactic.
(* Require Import MOmega. *)


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

(************************************** 
   Properties of order and product
 **************************************)

Theorem Zmult_interval: forall p q, 0 < p * q  -> 1 < p -> 0 < q < p * q.
intros p q H1 H2; assert (0 < q).
case (Zle_or_lt q 0); auto; intros H3; contradict H1; apply Zle_not_lt.
rewrite <- (Zmult_0_r p).
apply Zmult_le_compat_l; auto with zarith.
split; auto.
pattern q at 1; rewrite <- (Zmult_1_l q).
apply Zmult_lt_compat_r; auto with zarith.
Qed.

Theorem Zmult_lt_compat: forall n m p q : Z, 0 < n <= p -> 0 < m < q -> n * m < p * q.
intros n m p q (H1, H2) (H3, H4).
apply Zle_lt_trans with (p * m).
apply Zmult_le_compat_r; auto with zarith.
apply Zmult_lt_compat_l; auto with zarith.
Qed.

Theorem Zle_square_mult: forall a b, 0 <= a <= b -> a * a <= b * b.
intros a b (H1, H2); apply Zle_trans with (a * b); auto with zarith.
Qed.

Theorem Zlt_square_mult: forall a b, 0 <= a < b -> a * a < b * b.
intros a b (H1, H2); apply Zle_lt_trans with (a * b); auto with zarith.
apply Zmult_lt_compat_r; auto with zarith.
Qed.

Theorem Zlt_square_mult_inv: forall a b, 0 <= a -> 0 <= b -> a * a < b * b -> a < b.
intros a b H1 H2 H3; case (Zle_or_lt b a); auto; intros H4; apply Zmult_lt_reg_r with a; 
   contradict H3; apply Zle_not_lt; apply Zle_square_mult; auto.
Qed.


Theorem Zpower_2: forall x, x^2 = x * x.
intros; ring.
Qed.

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


(************************************** 
   Properties of Z_nat
 **************************************)
 
Theorem inj_eq_inv: forall (n m : nat), Z_of_nat n = Z_of_nat m ->  n = m.
intros n m H1; case (le_or_lt n m); auto with arith.
intros H2; case (le_lt_or_eq _ _ H2); auto; intros H3.
contradict H1; auto with zarith.
intros H2; contradict H1; auto with zarith.
Qed.
 
Theorem inj_le_inv: forall (n m : nat), Z_of_nat n <= Z_of_nat m->  (n <= m)%nat.
intros n m H1; case (le_or_lt n m); auto with arith.
intros H2; contradict H1; auto with zarith.
Qed.
 
Theorem Z_of_nat_Zabs_nat:
 forall (z : Z), 0 <= z ->  Z_of_nat (Zabs_nat z) = z.
intros z; case z; simpl; auto with zarith.
intros; apply sym_equal; apply Zpos_eq_Z_of_nat_o_nat_of_P; auto.
intros p H1; contradict H1; simpl; auto with zarith.
Qed.

(************************************** 
  Properties of Zabs
**************************************)
 
Theorem Zabs_square: forall a,  a * a = Zabs a * Zabs a.
intros a; rewrite <- Zabs_Zmult; apply sym_equal; apply Zabs_eq;
 auto with zarith.
case (Zle_or_lt 0%Z a); auto with zarith.
intros Ha; replace (a * a) with (- a * - a); auto with zarith.
ring.
Qed.

(************************************** 
  Properties of Zabs_nat
**************************************)
 
Theorem Z_of_nat_abs_le:
 forall x y, x <= y ->  x + Z_of_nat (Zabs_nat (y - x)) = y.
intros x y Hx1.
rewrite Z_of_nat_Zabs_nat; auto with zarith.
Qed.

Theorem Zabs_nat_Zsucc:
 forall p, 0 <= p ->  Zabs_nat (Zsucc p) = S (Zabs_nat p).
intros p Hp.
apply inj_eq_inv.
rewrite inj_S; (repeat rewrite Z_of_nat_Zabs_nat); auto with zarith.
Qed.

Theorem Zabs_nat_Z_of_nat: forall n, Zabs_nat (Z_of_nat n) = n.
intros n1; apply inj_eq_inv; rewrite Z_of_nat_Zabs_nat; auto with zarith.
Qed.
 

(************************************** 
  Properties Zsqrt_plain
**************************************)

Theorem Zsqrt_plain_is_pos: forall n, 0 <= n ->  0 <= Zsqrt_plain n.
intros n m; case (Zsqrt_interval n); auto with zarith.
intros H1 H2; case (Zle_or_lt 0 (Zsqrt_plain n)); auto.
intros H3; contradict H2; apply Zle_not_lt.
apply Zle_trans with ( 2 := H1 ).
replace ((Zsqrt_plain n + 1) * (Zsqrt_plain n + 1))
     with (Zsqrt_plain n * Zsqrt_plain n + (2 * Zsqrt_plain n + 1));
 auto with zarith.
ring.
Qed.

Theorem Zsqrt_square_id: forall a, 0 <= a ->  Zsqrt_plain (a * a) = a.
intros a H.
generalize (Zsqrt_plain_is_pos (a * a)); auto with zarith; intros Haa.
case (Zsqrt_interval (a * a)); auto with zarith.
intros H1 H2.
case (Zle_or_lt a (Zsqrt_plain (a * a))); intros H3; auto.
case Zle_lt_or_eq with ( 1 := H3 ); auto; clear H3; intros H3.
contradict H1; apply Zlt_not_le; auto with zarith.
apply Zle_lt_trans with (a * Zsqrt_plain (a * a)); auto with zarith.
apply Zmult_lt_compat_r; auto with zarith.
contradict H2; apply Zle_not_lt; auto with zarith.
apply Zmult_le_compat; auto with zarith.
Qed.
 
Theorem Zsqrt_le:
 forall p q, 0 <= p <= q  ->  Zsqrt_plain p <= Zsqrt_plain q.
intros p q [H1 H2]; case Zle_lt_or_eq with ( 1 := H2 ); clear H2; intros H2.
2:subst q; auto with zarith.
case (Zle_or_lt (Zsqrt_plain p) (Zsqrt_plain q)); auto; intros H3.
assert (Hp: (0 <= Zsqrt_plain q)).
apply Zsqrt_plain_is_pos; auto with zarith.
absurd (q <= p); auto with zarith.
apply Zle_trans with ((Zsqrt_plain q + 1) * (Zsqrt_plain q + 1)).
case (Zsqrt_interval q); auto with zarith.
apply Zle_trans with (Zsqrt_plain p * Zsqrt_plain p); auto with zarith.
apply Zmult_le_compat; auto with zarith.
case (Zsqrt_interval p); auto with zarith.
Qed.


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

Theorem Zpower_mult: forall p q r,  0 <= q -> 0 <=  r -> p ^ (q * r) = (p ^ q) ^ r.
intros p q r H1 H2; generalize H2; pattern r; apply natlike_ind; auto.
intros H3; rewrite Zmult_0_r; repeat rewrite Zpower_exp_0; auto.
intros r1 H3 H4 H5.
unfold Zsucc; rewrite Zpower_exp; auto with zarith.
rewrite <- H4; try rewrite Zpower_exp_1; try rewrite <- Zpower_exp; try eq_tac; auto with zarith.
ring.
apply Zle_ge; replace 0 with (0 * r1); try apply Zmult_le_compat_r; auto.
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

Theorem Zpower_lt_monotone: forall a b c: Z, 1 < a -> 0 <= b < c -> a ^ b < a ^ c.
intros a b c H (H1, H2).
rewrite <- (Zmult_1_r (a ^ b)); replace c with (b + (c - b)); auto with zarith.
rewrite Zpower_exp; auto with zarith.
apply Zmult_lt_compat_l; auto with zarith.
apply Zpower_lt_0; auto with zarith.
assert (0 < a ^ (c - b)); auto with zarith.
apply Zpower_lt_0; auto with zarith.
apply Zlt_le_trans with (a ^1); auto with zarith.
rewrite Zpower_exp_1; auto with zarith.
apply Zpower_le_monotone; auto with zarith.
Qed.

Theorem Zpower_nat_Zpower: forall p q, 0 <= q -> p ^ q = Zpower_nat p (Zabs_nat q).
intros p1 q1; case q1; simpl.
intros _; exact (refl_equal _).
intros p2 _; apply Zpower_pos_nat.
intros p2 H1; case H1; auto.
Qed.

Theorem Zgt_pow_1 : forall n m : Z, 0 < n -> 1 < m -> 1 < m ^ n.
Proof.
intros n m H1 H2.
replace 1 with (m ^ 0) by apply Zpower_exp_0.
apply Zpower_lt_monotone; auto with zarith.
Qed.

(************************************** 
  Properties Zmod 
**************************************)
 
Theorem Zmod_mult:
 forall a b n, 0 < n ->  (a * b) mod n = ((a mod n) * (b mod n)) mod n.
intros a b n H.
pattern a at 1; rewrite (Z_div_mod_eq a n); auto with zarith.
pattern b at 1; rewrite (Z_div_mod_eq b n); auto with zarith.
replace ((n * (a / n) + a mod n) * (n * (b / n) + b mod n))
     with
      ((a mod n) * (b mod n) +
       (((n * (a / n)) * (b / n) + (b mod n) * (a / n)) + (a mod n) * (b / n)) *
       n); auto with zarith.
apply Z_mod_plus; auto with zarith.
ring.
Qed.

Theorem Zmod_plus:
 forall a b n, 0 < n ->  (a + b) mod n = (a mod n + b mod n) mod n.
intros a b n H.
pattern a at 1; rewrite (Z_div_mod_eq a n); auto with zarith.
pattern b at 1; rewrite (Z_div_mod_eq b n); auto with zarith.
replace ((n * (a / n) + a mod n) + (n * (b / n) + b mod n))
     with ((a mod n + b mod n) + (a / n + b / n) * n); auto with zarith.
apply Z_mod_plus; auto with zarith.
ring.
Qed.

Theorem Zmod_mod: forall a n, 0 < n -> (a mod n) mod n = a mod n.
intros a n H.
pattern a at 2; rewrite (Z_div_mod_eq a n); auto with zarith.
rewrite Zplus_comm; rewrite Zmult_comm.
apply sym_equal; apply Z_mod_plus; auto with zarith.
Qed.
 
Theorem Zmod_def_small: forall a n, 0 <= a < n  ->  a mod n = a.
intros a n [H1 H2]; unfold Zmod.
generalize (Z_div_mod a n); case (Zdiv_eucl a n).
intros q r H3; case H3; clear H3; auto with zarith.
auto with zarith.
intros H4 [H5 H6].
case (Zle_or_lt q (- 1)); intros H7.
contradict H1; apply Zlt_not_le.
subst a.
apply Zle_lt_trans with (n * - 1 + r); auto with zarith.
case (Zle_lt_or_eq 0 q); auto with zarith; intros H8.
contradict H2; apply Zle_not_lt.
apply Zle_trans with (n * 1 + r); auto with zarith.
rewrite H4; auto with zarith.
subst a; subst q; auto with zarith.
Qed.

Theorem Zmod_minus: forall a b n, 0 < n -> (a - b) mod n = (a mod n - b mod n) mod n.
intros a b n H; replace (a - b) with (a + (-1) * b); auto with zarith.
replace (a mod n - b mod n) with (a mod n + (-1) * (b mod n)); auto with zarith.
rewrite Zmod_plus; auto with zarith.
rewrite Zmod_mult; auto with zarith.
rewrite (fun x y => Zmod_plus x  ((-1) * y)); auto with zarith.
rewrite Zmod_mult; auto with zarith.
rewrite (fun x => Zmod_mult x (b mod n)); auto with zarith.
repeat rewrite Zmod_mod; auto.
Qed.

Theorem Zmod_Zpower: forall p q n, 0 < n ->  (p ^ q) mod n = ((p mod n) ^ q) mod n.
intros p q n Hn; case (Zle_or_lt 0 q); intros H1.
generalize H1; pattern q; apply natlike_ind; auto.
intros q1 Hq1 Rec _; unfold Zsucc; repeat rewrite Zpower_exp; repeat rewrite Zpower_exp_1; auto with zarith.
rewrite (fun x => (Zmod_mult x p)); try rewrite Rec; auto.
rewrite (fun x y => (Zmod_mult (x ^y))); try eq_tac; auto.
eq_tac; auto; apply sym_equal; apply Zmod_mod; auto with zarith.
generalize H1; case q; simpl; auto.
intros; discriminate.
Qed.

Theorem Zmod_le: forall a n, 0 < n -> 0 <= a -> (Zmod a n) <= a.
intros a n H1 H2; case (Zle_or_lt n  a); intros H3.
case (Z_mod_lt a n); auto with zarith.
rewrite Zmod_def_small; auto with zarith.
Qed.

Lemma Zplus_mod_idemp_l: forall a b n, 0 < n -> (a mod n + b) mod n = (a + b) mod n.
Proof.
intros. rewrite Zmod_plus; auto.
rewrite Zmod_mod; auto.
symmetry; apply Zmod_plus; auto.
Qed.

Lemma Zplus_mod_idemp_r: forall a b n, 0 < n -> (b + a mod n) mod n = (b + a) mod n.
Proof.
intros a b n H; repeat rewrite (Zplus_comm b).
apply Zplus_mod_idemp_l; auto.
Qed.

Lemma Zminus_mod_idemp_l: forall a b n, 0 < n -> (a mod n - b) mod n = (a - b) mod n.
Proof.
intros. rewrite Zmod_minus; auto.
rewrite Zmod_mod; auto.
symmetry; apply Zmod_minus; auto.
Qed.

Lemma Zminus_mod_idemp_r: forall a b n, 0 < n -> (a - b mod n) mod n = (a - b) mod n.
Proof.
intros. rewrite Zmod_minus; auto.
rewrite Zmod_mod; auto.
symmetry; apply Zmod_minus; auto.
Qed.

Lemma Zmult_mod_idemp_l: forall a b n, 0 < n -> (a mod n * b) mod n = (a * b) mod n.
Proof.
intros; rewrite Zmod_mult; auto.
rewrite Zmod_mod; auto.
symmetry; apply Zmod_mult; auto.
Qed.

Lemma Zmult_mod_idemp_r: forall a b n, 0 < n -> (b * (a mod n)) mod n = (b * a) mod n.
Proof.
intros a b n H; repeat rewrite (Zmult_comm b).
apply Zmult_mod_idemp_l; auto.
Qed.

Lemma Zmod_div_mod: forall n m a, 0 < n -> 0 < m ->
  (n | m) -> a mod n = (a mod m) mod n.
Proof.
intros n m a H1 H2 H3.
pattern a at 1; rewrite (Z_div_mod_eq a m); auto with zarith.
case H3; intros q Hq; pattern m at 1; rewrite Hq.
rewrite (Zmult_comm q).
rewrite Zmod_plus; auto.
rewrite <- Zmult_assoc; rewrite Zmod_mult; auto.
rewrite Z_mod_same; try rewrite Zmult_0_l; auto with zarith.
rewrite (Zmod_def_small 0); auto with zarith.
rewrite Zplus_0_l; rewrite Zmod_mod; auto with zarith.
Qed.

(** A better way to compute Zpower mod **)

Fixpoint Zpow_mod_pos (a: Z) (m: positive)  (n : Z) {struct m} : Z :=
  match m with
  | xH => a mod n
  | xO m' =>
    let z := Zpow_mod_pos a m' n in
    match z with
    | 0 => 0
    | _ => (z * z) mod n
    end
  | xI m' =>
    let z := Zpow_mod_pos a m' n in
    match z with
    | 0 => 0
    | _ => (z * z * a) mod n
    end
  end.

Theorem Zpow_mod_pos_Zpower_pos_correct: forall a m n, 0 < n -> Zpow_mod_pos a m n = (Zpower_pos a m) mod n.
intros a m; elim m; simpl; auto.
intros p Rec n H1; rewrite xI_succ_xO; rewrite Pplus_one_succ_r; rewrite <- Pplus_diag; auto.
repeat rewrite Zpower_pos_is_exp; auto.
repeat rewrite Rec; auto.
replace (Zpower_pos a 1) with a; auto.
2: unfold Zpower_pos; simpl; auto with zarith.
repeat rewrite (fun x => (Zmod_mult x a)); auto. 
rewrite  (Zmod_mult  (Zpower_pos a p)); auto. 
case (Zpower_pos a p mod n); auto.
intros p Rec n H1; rewrite <- Pplus_diag; auto.
repeat rewrite Zpower_pos_is_exp; auto.
repeat rewrite Rec; auto.
rewrite  (Zmod_mult  (Zpower_pos a p)); auto. 
case (Zpower_pos a p mod n); auto.
unfold Zpower_pos; simpl; rewrite Zmult_1_r; auto with zarith.
Qed.

Definition Zpow_mod a m n := match m with 0 => 1 | Zpos p1 => Zpow_mod_pos a p1 n | Zneg p1 => 0 end.

Theorem Zpow_mod_Zpower_correct: forall a m n, 1 < n -> 0 <= m -> Zpow_mod a m n = (a ^ m) mod n.
intros a m n; case m; simpl.
intros; apply sym_equal; apply Zmod_def_small; auto with zarith.
intros; apply Zpow_mod_pos_Zpower_pos_correct; auto with zarith.
intros p H H1; case H1; auto.
Qed.

(* A direct way to compute Zmod *)

Fixpoint Zmod_POS (a : positive) (b : Z) {struct a} : Z  :=
  match a with
  | xI a' =>
      let r := Zmod_POS a' b in
      let r' := (2 * r + 1) in
      if Zgt_bool b r' then r' else (r' - b)
  | xO a' =>
      let r := Zmod_POS a' b in
      let r' := (2 * r) in
      if Zgt_bool b r' then r' else (r' - b)
  | xH => if Zge_bool b 2 then 1 else 0
  end.

Theorem Zmod_POS_correct: forall a b, Zmod_POS a b = (snd (Zdiv_eucl_POS a b)).
intros a b; elim a; simpl; auto.
intros p Rec; rewrite  Rec.
case (Zdiv_eucl_POS p b); intros z1 z2; simpl; auto.
match goal with |- context [Zgt_bool _ ?X] => case (Zgt_bool b X) end; auto.
intros p Rec; rewrite  Rec.
case (Zdiv_eucl_POS p b); intros z1 z2; simpl; auto.
match goal with |- context [Zgt_bool _ ?X] => case (Zgt_bool b X) end; auto.
case (Zge_bool b 2); auto.
Qed.

Definition Zmodd  a b :=
match a with
| Z0 => 0
| Zpos a' =>
    match b with
    | Z0 => 0
    | Zpos _ => Zmod_POS a' b
    | Zneg b' =>
        let r := Zmod_POS a' (Zpos b') in
        match r  with Z0 =>  0 |  _  =>   b + r end
    end
| Zneg a' =>
    match b with
    | Z0 => 0
    | Zpos _ =>
        let r := Zmod_POS a' b in
        match r with Z0 =>  0 | _  =>  b - r end
    | Zneg b' => - (Zmod_POS a' (Zpos b'))
    end
end.

Theorem Zmodd_correct: forall a b, Zmodd a b = Zmod a b.
intros a b; unfold Zmod; case a; simpl; auto.
intros p; case b; simpl; auto.
intros p1; refine (Zmod_POS_correct _ _); auto.
intros p1; rewrite Zmod_POS_correct; auto.
case (Zdiv_eucl_POS p (Zpos p1)); simpl; intros z1 z2; case z2; auto.
intros p; case b; simpl; auto.
intros p1; rewrite Zmod_POS_correct; auto.
case (Zdiv_eucl_POS p (Zpos p1)); simpl; intros z1 z2; case z2; auto.
intros p1; rewrite Zmod_POS_correct; simpl; auto.
case (Zdiv_eucl_POS p (Zpos p1)); auto.
Qed.

(**************************************
 Properties of Zdivide
**************************************)

Theorem Zmod_divide_minus: forall a b c : Z, 
 0 < b -> a mod b = c -> (b | a - c).
Proof.
  intros a b c H H1; apply Zmod_divide; auto with zarith.
  rewrite Zmod_minus; auto.
  rewrite H1; pattern c at 1; rewrite <- (Zmod_def_small c b); auto with zarith.
  rewrite Zminus_diag; apply Zmod_def_small; auto with zarith.
  subst; apply Z_mod_lt; auto with zarith.
Qed.

Theorem Zdivide_mod_minus: forall a b c : Z, 
 0 <= c < b -> (b | a -c) -> (a mod b) = c.
Proof.
  intros a b c (H1, H2) H3; assert (0 < b); try apply Zle_lt_trans with c; auto.
  replace a with ((a - c) + c); auto with zarith.
  rewrite Zmod_plus; auto with zarith.
  rewrite (Zdivide_mod (a -c) b); try rewrite Zplus_0_l; auto with zarith.
  rewrite Zmod_mod; try apply Zmod_def_small; auto with zarith.
Qed.

Theorem Zmod_closeby_eq: forall a b n,  0 <= a -> 0 <= b < n -> a - b < n -> a mod n = b -> a = b.
Proof.
  intros a b n H H1 H2 H3.
  case (Zle_or_lt 0 (a - b)); intros H4.
  case Zle_lt_or_eq with (1 := H4); clear H4; intros H4; auto with zarith.
  absurd_hyp H2; auto.
  apply Zle_not_lt; apply Zdivide_le; auto with zarith.
  apply Zmod_divide_minus; auto with zarith.
  rewrite <- (Zmod_def_small a n); try split; auto with zarith.
Qed.

Theorem Zpower_divide: forall p q, 0 < q -> (p | p ^ q).
Proof.
  intros p q H; exists (p ^(q - 1)).
  pattern p at 3; rewrite <- (Zpower_exp_1 p); rewrite <- Zpower_exp; try eq_tac; auto with zarith.
Qed.


(**************************************
 Properties of Zis_gcd 
**************************************)

(* P.L. : See Numtheory.v *)

(**************************************
  Properties rel_prime
**************************************)
 
Theorem rel_prime_sym: forall a b, rel_prime a b ->  rel_prime b a.
intros a b H; auto with zarith.
red; apply Zis_gcd_sym; auto with zarith.
Qed.
 
Theorem rel_prime_le_prime:
 forall a p, prime p -> 1 <=  a < p  ->  rel_prime a p.
intros a p Hp [H1 H2].
apply rel_prime_sym; apply prime_rel_prime; auto.
intros [q Hq]; subst a.
case (Zle_or_lt q 0); intros Hl.
absurd (q * p <= 0 * p); auto with zarith.
absurd (1 * p <= q * p); auto with zarith.
Qed.
 
Definition rel_prime_dec:
 forall a b,  ({ rel_prime a b }) + ({ ~ rel_prime a b }).
intros a b; case (Z_eq_dec (Zgcd a b) 1); intros H1.
left; red.
rewrite <- H1; apply Zgcd_is_gcd.
right; contradict H1.
case (Zis_gcd_unique a b (Zgcd a b) 1); auto.
apply Zgcd_is_gcd.
intros H2; absurd (0 <= Zgcd a b); auto with zarith.
generalize (Zgcd_is_pos a b); auto with zarith.
Qed.

Theorem rel_prime_mod_rev: forall p q, 0 < q -> rel_prime (p mod q) q -> rel_prime p q.
intros p q H H0.
rewrite (Z_div_mod_eq p q); auto with zarith.
red.
apply Zis_gcd_sym; apply Zis_gcd_for_euclid2; auto with zarith.
Qed.

Theorem rel_prime_div: forall p q r, rel_prime p q -> (r | p) -> rel_prime r q.
intros p q r H (u, H1); subst.
inversion_clear H as [H1 H2 H3].
red; apply Zis_gcd_intro; try apply Zone_divide.
intros x H4 H5; apply H3; auto.
apply Zdivide_mult_r; auto.
Qed.

Theorem rel_prime_1: forall n, rel_prime 1 n.
intros n; red; apply Zis_gcd_intro; auto.
exists 1; auto with zarith.
exists n; auto with zarith.
Qed.

Theorem not_rel_prime_0: forall n, 1 < n -> ~rel_prime 0 n.
intros n H H1; absurd (n = 1 \/ n = -1).
intros [H2 | H2]; subst; contradict H; auto with zarith.
case (Zis_gcd_unique  0 n n 1); auto.
apply Zis_gcd_intro; auto.
exists 0; auto with zarith.
exists 1; auto with zarith.
Qed.

Theorem rel_prime_mod: forall p q, 0 < q -> rel_prime p q -> rel_prime (p mod q) q.
intros p q H H0.
assert (H1: Bezout p q 1).
apply rel_prime_bezout; auto.
inversion_clear H1 as [q1 r1 H2].
apply bezout_rel_prime.
apply Bezout_intro with q1  (r1 + q1 * (p / q)).
rewrite <- H2.
pattern p at 3; rewrite (Z_div_mod_eq p q); try ring; auto with zarith.
Qed.

Theorem Zrel_prime_neq_mod_0: forall a b, 1 < b -> rel_prime a b -> a mod b <> 0.
Proof.
intros a b H H1 H2.
case (not_rel_prime_0 _ H).
rewrite <- H2.
apply rel_prime_mod; auto with zarith.
Qed.

Theorem rel_prime_Zpower_r: forall i p q, 0 < i -> rel_prime p q -> rel_prime p (q^i).
intros i p q Hi Hpq; generalize Hi; pattern i; apply natlike_ind; auto with zarith; clear i Hi.
intros H; contradict H; auto with zarith.
intros i Hi Rec _; rewrite Zpower_Zsucc; auto.
apply rel_prime_mult; auto.
case Zle_lt_or_eq with (1 := Hi); intros Hi1; subst; auto.
rewrite Zpower_exp_0; apply rel_prime_sym; apply rel_prime_1.
Qed.


(************************************** 
  Properties prime 
**************************************)
 
Theorem not_prime_0: ~ prime 0.
intros H1; case (prime_divisors _ H1 2); auto with zarith.
Qed.

 
Theorem not_prime_1: ~ prime 1.
intros H1; absurd (1 < 1); auto with zarith.
inversion H1; auto.
Qed.
 
Theorem prime_2: prime 2.
apply prime_intro; auto with zarith.
intros n [H1 H2]; case Zle_lt_or_eq with ( 1 := H1 ); auto with zarith;
 clear H1; intros H1.
contradict H2; auto with zarith.
subst n; red; auto with zarith.
apply Zis_gcd_intro; auto with zarith.
Qed.
 
Theorem prime_3: prime 3.
apply prime_intro; auto with zarith.
intros n [H1 H2]; case Zle_lt_or_eq with ( 1 := H1 ); auto with zarith;
 clear H1; intros H1.
case (Zle_lt_or_eq 2 n); auto with zarith; clear H1; intros H1.
contradict H2; auto with zarith.
subst n; red; auto with zarith.
apply Zis_gcd_intro; auto with zarith.
intros x [q1 Hq1] [q2 Hq2].
exists (q2 - q1).
apply trans_equal with (3 - 2); auto with zarith.
rewrite Hq1; rewrite Hq2; ring.
subst n; red; auto with zarith.
apply Zis_gcd_intro; auto with zarith.
Qed.
 
Theorem prime_le_2: forall p, prime p ->  2 <= p.
intros p Hp; inversion Hp; auto with zarith.
Qed.
 
Definition prime_dec_aux:
 forall p m,
  ({ forall n,  1 < n < m  ->  rel_prime n p }) +
  ({ exists n , 1 < n < m  /\ ~ rel_prime n p  }).
intros p m.
case (Z_lt_dec 1 m); intros H1.
apply natlike_rec
     with
      ( P :=
      fun m =>
      ({ forall (n : Z), 1 < n < m  ->  rel_prime n p }) +
      ({ exists n : Z , 1 < n < m  /\ ~ rel_prime n p  }) );
 auto with zarith.
left; intros n [HH1 HH2]; contradict HH2; auto with zarith.
intros x Hx Rec; case Rec.
intros P1; case (rel_prime_dec x p); intros P2.
left; intros n [HH1 HH2].
case (Zgt_succ_gt_or_eq x n); auto with zarith.
intros HH3; subst x; auto.
case (Z_lt_dec 1 x); intros HH1.
right; exists x; split; auto with zarith.
left; intros n [HHH1 HHH2]; contradict HHH1; auto with zarith.
intros tmp; right; case tmp; intros n [HH1 HH2]; exists n; auto with zarith.
left; intros n [HH1 HH2]; contradict H1; auto with zarith.
Defined.
 
Theorem not_prime_divide:
 forall p, 1 < p -> ~ prime p -> exists n, 1 < n < p  /\ (n | p) .
intros p Hp Hp1.
case (prime_dec_aux p p); intros H1.
case Hp1; apply prime_intro; auto.
intros n [Hn1 Hn2].
case Zle_lt_or_eq with ( 1 := Hn1 ); auto with zarith.
intros H2; subst n; red; apply Zis_gcd_intro; auto with zarith.
case H1; intros n [Hn1 Hn2].
generalize (Zgcd_is_pos n p); intros Hpos.
case (Zle_lt_or_eq 0 (Zgcd n p)); auto with zarith; intros H3.
case (Zle_lt_or_eq 1 (Zgcd n p)); auto with zarith; intros H4.
exists (Zgcd n p); split; auto.
split; auto.
apply Zle_lt_trans with n; auto with zarith.
generalize (Zgcd_is_gcd n p); intros tmp; inversion_clear tmp as [Hr1 Hr2 Hr3].
case Hr1; intros q Hq.
case (Zle_or_lt q 0); auto with zarith; intros Ht.
absurd (n <= 0 * Zgcd n p) ; auto with zarith.
pattern n at 1; rewrite Hq; auto with zarith.
apply Zle_trans with (1 * Zgcd n p); auto with zarith.
pattern n at 2; rewrite Hq; auto with zarith.
generalize (Zgcd_is_gcd n p); intros Ht; inversion Ht; auto.
case Hn2; red.
rewrite H4; apply Zgcd_is_gcd.
generalize (Zgcd_is_gcd n p); rewrite <- H3; intros tmp;
 inversion_clear tmp as [Hr1 Hr2 Hr3].
absurd (n = 0); auto with zarith.
case Hr1; auto with zarith.
Defined.
 
Definition prime_dec: forall p,  ({ prime p }) + ({ ~ prime p }).
intros p; case (Z_lt_dec 1 p); intros H1.
case (prime_dec_aux p p); intros H2.
left; apply prime_intro; auto.
intros n [Hn1 Hn2]; case Zle_lt_or_eq with ( 1 := Hn1 ); auto.
intros HH; subst n.
red; apply Zis_gcd_intro; auto with zarith.
right; intros H3; inversion_clear H3 as [Hp1 Hp2].
case H2; intros n [Hn1 Hn2]; case Hn2; auto with zarith.
right; intros H3; inversion_clear H3 as [Hp1 Hp2]; case H1; auto.
Defined.

 
Theorem prime_def:
 forall p, 1 < p -> (forall n,  1 < n < p  ->  ~ (n | p)) ->  prime p.
intros p H1 H2.
apply prime_intro; auto.
intros n H3.
red; apply Zis_gcd_intro; auto with zarith.
intros x H4 H5.
case (Zle_lt_or_eq 0 (Zabs x)); auto with zarith; intros H6.
case (Zle_lt_or_eq 1 (Zabs x)); auto with zarith; intros H7.
case (Zle_lt_or_eq (Zabs x) p); auto with zarith.
apply Zdivide_le; auto with zarith.
apply Zdivide_Zabs_inv_l; auto.
intros H8; case (H2 (Zabs x)); auto.
apply Zdivide_Zabs_inv_l; auto.
intros H8; subst p; absurd (Zabs x <= n); auto with zarith.
apply Zdivide_le; auto with zarith.
apply Zdivide_Zabs_inv_l; auto.
rewrite H7; pattern (Zabs x); apply Zabs_intro; auto with zarith.
absurd (0%Z = p); auto with zarith.
cut (Zdivide (Zabs x) p).
intros [q Hq]; subst p; rewrite <- H6; auto with zarith.
apply Zdivide_Zabs_inv_l; auto.
Qed.
 
Theorem prime_inv_def: forall p n, prime p -> 1 < n < p  ->  ~ (n | p).
intros p n H1 H2 H3.
absurd (rel_prime n p); auto.
unfold rel_prime; intros H4.
case (Zis_gcd_unique n p n 1); auto with zarith.
apply Zis_gcd_intro; auto with zarith.
inversion H1; auto with zarith.
Qed.
 
Theorem square_not_prime: forall a,  ~ prime (a * a).
intros a; rewrite (Zabs_square a).
case (Zle_lt_or_eq 0 (Zabs a)); auto with zarith; intros Hza1.
case (Zle_lt_or_eq 1 (Zabs a)); auto with zarith; intros Hza2.
intros Ha; case (prime_inv_def (Zabs a * Zabs a) (Zabs a)); auto.
split; auto.
pattern (Zabs a) at 1; replace (Zabs a) with (1 * Zabs a); auto with zarith.
apply Zmult_lt_compat_r; auto with zarith.
exists (Zabs a); auto.
rewrite <- Hza2; simpl; apply not_prime_1.
rewrite <- Hza1; simpl; apply not_prime_0.
Qed.

Theorem prime_divide_prime_eq:
 forall p1 p2, prime p1 -> prime p2 -> Zdivide p1 p2 ->  p1 = p2.
intros p1 p2 Hp1 Hp2 Hp3.
assert (Ha: 1 < p1).
inversion Hp1; auto.
assert (Ha1: 1 < p2).
inversion Hp2; auto.
case (Zle_lt_or_eq p1 p2); auto with zarith.
apply Zdivide_le; auto with zarith.
intros Hp4.
case (prime_inv_def p2 p1); auto with zarith.
Qed.

Theorem Zdivide_div_prime_le_square:  forall x, 1 < x -> ~prime x -> exists p, prime p /\ (p | x) /\ p * p <= x.
intros x Hx; generalize Hx; pattern x; apply Z_lt_induction; auto with zarith.
clear x Hx; intros x Rec H H1.
case (not_prime_divide x); auto.
intros x1 ((H2, H3), H4); case (prime_dec x1); intros H5.
case (Zle_or_lt (x1 * x1) x); intros H6.
exists x1; auto.
case H4; clear H4; intros x2 H4; subst.
assert (Hx2: x2 <= x1).
case (Zle_or_lt x2 x1); auto; intros H8; contradict H6; apply Zle_not_lt.
apply Zmult_le_compat_r; auto with zarith.
case (prime_dec x2); intros H7.
exists x2; repeat (split; auto with zarith).
apply Zmult_le_compat_l; auto with zarith.
apply Zle_trans with 2%Z; try apply prime_le_2; auto with zarith.
case (Zle_or_lt 0 x2); intros H8.
case Zle_lt_or_eq with (1 := H8); auto with zarith; clear H8; intros H8; subst; auto with zarith.
case (Zle_lt_or_eq 1 x2); auto with zarith; clear H8; intros H8; subst; auto with zarith.
case (Rec x2); try split; auto with zarith.
intros x3 (H9, (H10, H11)).
exists x3; repeat (split; auto with zarith).
contradict H; apply Zle_not_lt; auto with zarith.
apply Zle_trans with (0 * x1);  auto with zarith.
case (Rec x1); try split; auto with zarith.
intros x3 (H9, (H10, H11)).
exists x3; repeat (split; auto with zarith).
apply Zdivide_trans with x1; auto with zarith.
Qed.

Theorem prime_div_prime: forall p q, prime p -> prime q -> (p | q) -> p = q.
intros p q H H1 H2; 
assert (Hp: 0 < p); try apply Zlt_le_trans with 2; try apply prime_le_2; auto with zarith.
assert (Hq: 0 < q); try apply Zlt_le_trans with 2; try apply prime_le_2; auto with zarith.
case prime_divisors with (2 := H2); auto.
intros H4; contradict Hp; subst; auto with zarith.
intros [H4| [H4 | H4]]; subst; auto.
contradict H; apply not_prime_1.
contradict Hp; auto with zarith.
Qed.

Theorem prime_div_Zpower_prime: forall n p q, 0 <= n -> prime p -> prime q -> (p | q ^ n) -> p = q.
intros n p q Hp Hq; generalize p q Hq; pattern n; apply natlike_ind; auto; clear n p q Hp Hq.
intros  p q Hp Hq; rewrite Zpower_exp_0.
intros (r, H); subst.
case (Zmult_interval p r); auto; try rewrite Zmult_comm.
rewrite <- H; auto with zarith.
apply Zlt_le_trans with 2; try apply prime_le_2; auto with zarith.
rewrite <- H; intros H1 H2; contradict H2; auto with zarith.
intros n1 H Rec p q Hp Hq; try rewrite Zpower_Zsucc; auto with zarith; intros H1.
case prime_mult with (2 := H1); auto.
intros H2; apply prime_div_prime; auto.
Qed.

Theorem rel_prime_Zpower: forall i j p q, 0 <= i ->  0 <= j -> rel_prime p q -> rel_prime (p^i) (q^j).
intros i j p q Hi; generalize Hi j p q; pattern i; apply natlike_ind; auto with zarith; clear i Hi j p q.
intros _ j p q H H1; rewrite Zpower_exp_0; apply rel_prime_1.
intros n Hn Rec _ j p q Hj Hpq.
rewrite Zpower_Zsucc; auto.
case Zle_lt_or_eq with (1 := Hj); intros Hj1; subst.
apply rel_prime_sym; apply rel_prime_mult; auto.
apply rel_prime_sym; apply rel_prime_Zpower_r; auto with arith.
apply rel_prime_sym; apply Rec; auto.
rewrite Zpower_exp_0; apply rel_prime_sym; apply rel_prime_1.
Qed.

Theorem prime_induction: forall (P: Z -> Prop), P 0 -> P 1 -> (forall p q, prime p -> P q -> P (p * q)) -> forall p, 0 <= p -> P p. 
intros P H H1 H2 p Hp.
generalize Hp; pattern p; apply Z_lt_induction; auto; clear p Hp.
intros p Rec Hp.
case Zle_lt_or_eq with (1 := Hp); clear Hp; intros Hp; subst; auto.
case (Zle_lt_or_eq  1 p); auto with zarith; clear Hp; intros Hp; subst; auto.
case (prime_dec p); intros H3.
rewrite <- (Zmult_1_r p); apply H2; auto.
 case (Zdivide_div_prime_le_square p); auto.
intros q (Hq1, ((q2, Hq2), Hq3)); subst.
case (Zmult_interval q q2).
rewrite Zmult_comm; apply Zlt_trans with 1; auto with zarith.
apply Zlt_le_trans with 2; auto with zarith; apply prime_le_2; auto.
intros H4 H5; rewrite Zmult_comm; apply H2; auto.
apply Rec; try split; auto with zarith.
rewrite Zmult_comm; auto.
Qed.

Theorem div_power_max: forall p q, 1 < p -> 0 < q -> exists n, 0 <= n /\ (p ^n | q)  /\ ~(p ^(1 + n) | q).
intros p q H1 H2; generalize H2; pattern q; apply Z_lt_induction; auto with zarith; clear q H2.
intros q Rec H2.
case (Zdivide_dec p q); intros H3.
case (Zdivide_Zdiv_lt_pos p q); auto with zarith; intros H4 H5.
case (Rec (Zdiv q p)); auto with zarith.
intros n (Ha1, (Ha2, Ha3)); exists (n + 1); split; auto with zarith; split.
case Ha2; intros q1 Hq; exists q1.
rewrite Zpower_exp; try rewrite Zpower_exp_1; auto with zarith.
rewrite  Zmult_assoc; rewrite <- Hq.
rewrite Zmult_comm; apply Zdivide_Zdiv_eq; auto with zarith.
intros (q1, Hu); case Ha3; exists q1.
apply Zmult_reg_r with p; auto with zarith.
rewrite (Zmult_comm (q / p)); rewrite <- Zdivide_Zdiv_eq; auto with zarith.
apply trans_equal with (1 := Hu); repeat rewrite Zpower_exp; try rewrite Zpower_exp_1; auto with zarith.
ring.
exists 0; repeat split; try rewrite Zpower_exp_1; try rewrite Zpower_exp_0; auto with zarith.
Qed.

Theorem prime_divide_Zpower_Zdiv: forall m a p i, 0 <= i -> prime p -> (m | a) -> ~(m | (a/p)) -> (p^i | a) -> (p^i | m).
intros m a p i Hi Hp (k, Hk) H (l, Hl); subst.
case (Zle_lt_or_eq 0 i); auto with arith; intros Hi1; subst.
assert (Hp0: 0 < p).
apply Zlt_le_trans with 2; auto with zarith; apply prime_le_2; auto.
case (Zdivide_dec p k); intros H1.
case H1; intros k' H2; subst.
case H; replace (k' * p * m) with ((k' * m) * p); try ring; rewrite Z_div_mult; auto with zarith.
apply Gauss with k.
exists l; rewrite Hl; ring.
apply rel_prime_sym; apply rel_prime_Zpower_r; auto.
apply rel_prime_sym; apply prime_rel_prime; auto.
rewrite Zpower_exp_0; apply Zone_divide.
Qed.


Theorem Zdivide_Zpower: forall n m, 0 < n -> (forall p i, prime p -> 0 < i -> (p^i | n) -> (p^i | m)) -> (n | m).
intros n m Hn; generalize m Hn; pattern n; apply prime_induction; auto with zarith; clear n m Hn.
intros m H1; contradict H1; auto with zarith.
intros p q H Rec m H1 H2.
assert (H3: (p | m)).
rewrite <- (Zpower_exp_1 p); apply H2; auto with zarith; rewrite Zpower_exp_1; apply Zdivide_factor_r.
case (Zmult_interval p q); auto.
apply Zlt_le_trans with 2; auto with zarith; apply prime_le_2; auto.
case H3; intros k Hk; subst.
intros Hq Hq1.
rewrite (Zmult_comm k); apply Zmult_divide_compat_l.
apply Rec; auto.
intros p1 i Hp1 Hp2 Hp3.
case (Z_eq_dec p p1); intros Hpp1; subst.
case (H2 p1 (Zsucc i)); auto with zarith.
rewrite Zpower_Zsucc; try apply Zmult_divide_compat_l; auto with zarith.
intros q2 Hq2; exists q2.
apply Zmult_reg_r with p1.
contradict H; subst; apply not_prime_0.
rewrite Hq2; rewrite Zpower_Zsucc; try ring; auto with zarith.
apply Gauss with p.
rewrite Zmult_comm; apply H2; auto.
apply Zdivide_trans with (1:= Hp3).
apply Zdivide_factor_l.
apply rel_prime_sym; apply rel_prime_Zpower_r; auto.
apply prime_rel_prime; auto.
contradict Hpp1; apply prime_divide_prime_eq; auto.
Qed.

Theorem divide_prime_divide: 
  forall a n m, 0 < a -> (n | m) -> (a | m) ->
  (forall p, prime p -> (p | a) -> ~(n | (m/p))) ->
  (a | n).
intros a n m Ha Hnm Ham Hp.
apply Zdivide_Zpower; auto.
intros p i H1 H2 H3.
apply prime_divide_Zpower_Zdiv with m; auto with zarith.
apply Hp; auto; apply Zdivide_trans with (2 := H3); auto.
apply Zpower_divide; auto.
apply Zdivide_trans with (1 := H3); auto.
Qed.

Theorem prime_div_induction: 
  forall (P: Z -> Prop) n,
    0 < n ->
    (P 1) ->
    (forall p i, prime p -> 0 <= i -> (p^i | n) -> P (p^i)) ->  
    (forall p q, rel_prime p q -> P p -> P q -> P (p * q)) -> 
   forall m, 0 <= m -> (m | n) -> P m. 
intros P n P1 Hn H H1 m Hm.
generalize Hm; pattern m; apply Z_lt_induction; auto; clear m Hm.
intros m Rec Hm H2.
case (prime_dec m); intros Hm1.
rewrite <- Zpower_exp_1; apply H; auto with zarith.
rewrite Zpower_exp_1; auto.
case Zle_lt_or_eq with (1 := Hm); clear Hm; intros Hm; subst.
2: contradict P1; case H2; intros; subst; auto with zarith.
case (Zle_lt_or_eq 1 m); auto with zarith; clear Hm; intros Hm; subst; auto.
case Zdivide_div_prime_le_square with m; auto.
intros p (Hp1, (Hp2, Hp3)).
case (div_power_max p m); auto with zarith.
generalize (prime_le_2 p Hp1); auto with zarith.
intros i (Hi, (Hi1, Hi2)).
case Zle_lt_or_eq with (1 := Hi); clear Hi; intros Hi.
assert (Hpi: 0 < p ^ i).
apply Zpower_lt_0; auto with zarith.
apply Zlt_le_trans with 2; try apply prime_le_2; auto with zarith.
rewrite (Z_div_exact_2 m (p ^ i)); auto with zarith. 
apply H1; auto with zarith.
apply rel_prime_sym; apply rel_prime_Zpower_r; auto.
apply rel_prime_sym.
apply prime_rel_prime; auto.
contradict Hi2.
case Hi1; intros; subst.
rewrite Z_div_mult in Hi2; auto with zarith.
case Hi2; intros q0 Hq0; subst.
exists q0; rewrite Zpower_exp; try rewrite Zpower_exp_1; auto with zarith.
apply H; auto with zarith.
apply Zdivide_trans with (1 := Hi1); auto.
apply Rec; auto with zarith.
split; auto with zarith.
apply Zge_le; apply Z_div_ge0; auto with zarith.
apply Z_div_lt; auto with zarith.
apply Zle_ge; apply Zle_trans with p.
apply prime_le_2; auto.
pattern p at 1; rewrite <- Zpower_exp_1; apply Zpower_le_monotone; auto with zarith.
apply Zlt_le_trans with 2; try apply prime_le_2; auto with zarith.
apply Zge_le; apply Z_div_ge0; auto with zarith.
apply Zdivide_trans with (2 := H2); auto.
exists (p ^ i); apply Z_div_exact_2; auto with zarith.
apply Zdivide_mod; auto with zarith.
apply Zdivide_mod; auto with zarith.
case Hi2; rewrite <- Hi; rewrite Zplus_0_r; rewrite Zpower_exp_1; auto.
Qed.

(************************************** 
  A tail recursive way of compute a^n
**************************************)

Fixpoint Zpower_tr_aux (z1 z2: Z) (n: nat) {struct n}: Z :=
  match n with O => z1 | (S n1) => Zpower_tr_aux (z2 * z1) z2 n1 end.

Theorem Zpower_tr_aux_correct:
forall z1 z2 n p, z1 = Zpower_nat z2 p -> Zpower_tr_aux z1 z2 n = Zpower_nat z2 (p + n). 
intros z1 z2 n; generalize z1; elim n; clear z1 n; simpl; auto.
intros z1 p; rewrite plus_0_r; auto.
intros n1 Rec z1 p H1.
rewrite Rec with (p:= S p).
rewrite <- plus_n_Sm; simpl; auto.
pattern z2 at 1; replace z2 with (Zpower_nat z2 1).
rewrite H1; rewrite <- Zpower_nat_is_exp; simpl; auto.
unfold Zpower_nat; simpl; rewrite Zmult_1_r; auto.
Qed.

Definition Zpower_nat_tr := Zpower_tr_aux 1.

Theorem Zpower_nat_tr_correct:
forall z n, Zpower_nat_tr z n = Zpower_nat z n.
intros z n; unfold Zpower_nat_tr.
rewrite Zpower_tr_aux_correct with (p := 0%nat); auto.
Qed.


(************************************** 
  Definition of Zsquare 
**************************************)

Fixpoint Psquare (p: positive): positive :=
match p with
  xH => xH
| xO p => xO (xO (Psquare p))
| xI p => xI (xO (Pplus (Psquare p) p))
end.

Theorem Psquare_correct: (forall p, Psquare p = p * p)%positive.
intros p; elim p; simpl; auto.
intros p1 Rec; rewrite Rec.
eq_tac.
apply trans_equal with (xO p1 + xO (p1 * p1) )%positive; auto.
rewrite (Pplus_comm (xO p1)); auto.
rewrite Pmult_xI_permute_r; rewrite Pplus_assoc.
eq_tac; auto.
apply sym_equal; apply Pplus_diag.
intros p1 Rec; rewrite Rec; simpl; auto.
eq_tac; auto.
apply sym_equal; apply Pmult_xO_permute_r.
Qed.

Definition Zsquare p :=
match p with Z0 => Z0 | Zpos p => Zpos (Psquare p) | Zneg p => Zpos (Psquare p) end.

Theorem Zsquare_correct: forall p, Zsquare p = p * p.
intro p; case p; simpl; auto; intros p1; rewrite Psquare_correct; auto.
Qed.

(************************************** 
  Some properties of Zpower
**************************************)

Theorem prime_power_2: forall x n, 0 <= n -> prime x -> (x | 2 ^ n)  -> x = 2.
intros x n H Hx; pattern n; apply natlike_ind; auto; clear n H.
rewrite Zpower_exp_0.
intros H1; absurd (x <= 1).
apply Zlt_not_le; apply Zlt_le_trans with 2%Z; auto with zarith.
apply prime_le_2; auto.
apply Zdivide_le; auto with zarith.
apply Zle_trans with 2%Z; try apply prime_le_2; auto with zarith.
intros n1 H H1.
unfold Zsucc; rewrite Zpower_exp; try rewrite Zpower_exp_1; auto with zarith.
intros H2; case prime_mult with (2 := H2); auto.
intros H3; case (Zle_lt_or_eq x 2); auto.
apply Zdivide_le; auto with zarith.
apply Zle_trans with 2%Z; try apply prime_le_2; auto with zarith.
intros H4; contradict H4; apply Zle_not_lt.
apply prime_le_2; auto with zarith.
Qed.

Theorem Zdivide_power_2: forall x n, 0 <= n -> 0 <= x -> (x  | 2 ^ n) -> exists q, x = 2 ^ q. 
intros x n Hn H; generalize n H Hn; pattern x; apply Z_lt_induction; auto; clear x n H Hn. 
intros x Rec n H Hn  H1.
case Zle_lt_or_eq with (1 := H); auto; clear H; intros H; subst.
case (Zle_lt_or_eq 1 x); auto with zarith; clear H; intros H; subst.
case (prime_dec x); intros H2.
exists 1; simpl; apply prime_power_2 with n; auto.
case not_prime_divide with (2 := H2); auto.
intros p1 ((H3, H4), (q1, Hq1)); subst.
case (Rec p1) with n; auto with zarith.
apply Zdivide_trans with (2 := H1); exists q1; auto with zarith.
intros r1 Hr1.
case (Rec q1) with n; auto with zarith.
case (Zle_lt_or_eq 0 q1).
apply Zmult_le_0_reg_r with p1; auto with zarith.
split; auto with zarith.
pattern q1 at 1; replace q1 with (q1 * 1); auto with zarith.
apply Zmult_lt_compat_l; auto with zarith.
intros H5; subst; contradict H; auto with zarith.
apply Zmult_le_0_reg_r with p1; auto with zarith.
apply Zdivide_trans with (2 := H1); exists p1; auto with zarith.
intros r2 Hr2; exists (r2 + r1); subst.
apply sym_equal; apply Zpower_exp.
generalize H; case r2; simpl; auto with zarith.
intros; red; simpl; intros; discriminate.
generalize H; case r1; simpl; auto with zarith.
intros; red; simpl; intros; discriminate.
exists 0; simpl; auto.
case H1; intros q1; try rewrite Zmult_0_r; intros H2.
absurd (0 < 0); auto with zarith.
pattern 0 at 2; rewrite <- H2; auto with zarith.
apply Zpower_lt_0; auto with zarith.
Qed.


(************************************** 
  Some properties of Zodd and Zeven
**************************************)

Theorem Zeven_ex: forall p, Zeven p -> exists q, p = 2 * q.
intros p; case p; simpl; auto.
intros _; exists 0; auto.
intros p1; case p1; try ((intros H; case H; fail) || intros z H; case H; fail).
intros p2 _; exists (Zpos p2); auto.
intros p1; case p1; try ((intros H; case H; fail) || intros z H; case H; fail).
intros p2 _; exists (Zneg p2); auto.
Qed.

Theorem Zodd_ex: forall p, Zodd p -> exists q, p = 2 * q + 1.
intros p HH; case (Zle_or_lt 0 p); intros HH1.
exists (Zdiv2 p); apply Zodd_div2; auto with zarith.
exists ((Zdiv2 p) - 1); pattern p at 1; rewrite Zodd_div2_neg; auto with zarith.
Qed.

Theorem Zeven_2p: forall p, Zeven (2 * p).
intros p; case p; simpl; auto.
Qed.

Theorem Zodd_2p_plus_1: forall p, Zodd (2 * p + 1).
intros p; case p; simpl; auto.
intros p1; case p1; simpl; auto.
Qed.

Theorem Zeven_plus_Zodd_Zodd: forall z1 z2, Zeven z1 -> Zodd z2 -> Zodd (z1 + z2).
intros z1 z2 HH1 HH2; case Zeven_ex with (1 := HH1); intros x HH3; try rewrite HH3; auto.
case Zodd_ex with (1 := HH2); intros y HH4; try rewrite HH4; auto.
replace (2 * x + (2 * y + 1)) with (2 * (x + y) + 1); try apply Zodd_2p_plus_1; auto with zarith.
Qed.

Theorem Zeven_plus_Zeven_Zeven: forall z1 z2, Zeven z1 -> Zeven z2 -> Zeven (z1 + z2).
intros z1 z2 HH1 HH2; case Zeven_ex with (1 := HH1); intros x HH3; try rewrite HH3; auto.
case Zeven_ex with (1 := HH2); intros y HH4; try rewrite HH4; auto.
replace (2 * x + 2 * y) with (2 * (x + y)); try apply Zeven_2p; auto with zarith.
Qed.

Theorem Zodd_plus_Zeven_Zodd: forall z1 z2, Zodd z1 -> Zeven z2 -> Zodd (z1 + z2).
intros z1 z2 HH1 HH2; rewrite Zplus_comm; apply Zeven_plus_Zodd_Zodd; auto.
Qed.

Theorem Zodd_plus_Zodd_Zeven: forall z1 z2, Zodd z1 -> Zodd z2 -> Zeven (z1 + z2).
intros z1 z2 HH1 HH2; case Zodd_ex with (1 := HH1); intros x HH3; try rewrite HH3; auto.
case Zodd_ex with (1 := HH2); intros y HH4; try rewrite HH4; auto.
replace ((2 * x + 1) + (2 * y + 1)) with (2 * (x + y + 1)); try apply Zeven_2p; try ring.
Qed.

Theorem Zeven_mult_Zeven_l: forall z1 z2, Zeven z1 -> Zeven (z1 * z2).
intros z1 z2 HH1; case Zeven_ex with (1 := HH1); intros x HH3; try rewrite HH3; auto.
replace (2 * x * z2) with (2 * (x * z2)); try apply Zeven_2p; auto with zarith.
Qed.

Theorem Zeven_mult_Zeven_r: forall z1 z2, Zeven z2 -> Zeven (z1 * z2).
intros z1 z2 HH1; case Zeven_ex with (1 := HH1); intros x HH3; try rewrite HH3; auto.
replace (z1 * (2 * x)) with (2 * (x * z1)); try apply Zeven_2p; try ring.
Qed.

Theorem Zodd_mult_Zodd_Zodd: forall z1 z2, Zodd z1 -> Zodd z2 -> Zodd (z1 * z2).
intros z1 z2 HH1 HH2; case Zodd_ex with (1 := HH1); intros x HH3; try rewrite HH3; auto.
case Zodd_ex with (1 := HH2); intros y HH4; try rewrite HH4; auto.
replace ((2 * x + 1) * (2 * y + 1)) with (2 * (2 * x * y + x + y) + 1); try apply Zodd_2p_plus_1; try ring.
Qed.

Definition Zmult_lt_0_compat := Zmult_lt_O_compat.

Hint Rewrite Zmult_1_r Zmult_0_r Zmult_1_l Zmult_0_l Zplus_0_l Zplus_0_r Zminus_0_r: rm10.
Hint Rewrite Zmult_plus_distr_r Zmult_plus_distr_l Zmult_minus_distr_r Zmult_minus_distr_l: distr.

Theorem Zmult_lt_compat_bis:
    forall n m p q : Z, 0 <= n < p -> 0 <= m < q -> n * m < p * q.
intros n m p q (H1, H2) (H3,H4).
case Zle_lt_or_eq with (1 := H1); intros H5; auto with zarith.
case Zle_lt_or_eq with (1 := H3); intros H6; auto with zarith.
apply Zlt_trans with (n * q).
apply Zmult_lt_compat_l; auto.
apply Zmult_lt_compat_r; auto with zarith.
rewrite <- H6; autorewrite with rm10; apply Zmult_lt_0_compat; auto with zarith.
rewrite <- H5; autorewrite with rm10; apply Zmult_lt_0_compat; auto with zarith.
Qed.


Theorem nat_of_P_xO: 
  forall p,  nat_of_P (xO p) =  (2 * nat_of_P p)%nat.
intros p; unfold nat_of_P; simpl; rewrite Pmult_nat_2_mult_2_permute; auto with arith.
Qed.

Theorem nat_of_P_xI: 
  forall p,  nat_of_P (xI p) =  (2 * nat_of_P p + 1)%nat.
intros p; unfold nat_of_P; simpl; rewrite Pmult_nat_2_mult_2_permute; auto with arith.
ring.
Qed.

Theorem nat_of_P_xH: nat_of_P xH = 1%nat.
trivial.
Qed.

Hint Rewrite
  nat_of_P_xO nat_of_P_xI nat_of_P_xH
  nat_of_P_succ_morphism
  nat_of_P_plus_carry_morphism
  nat_of_P_plus_morphism
  nat_of_P_mult_morphism
  nat_of_P_minus_morphism: pos_morph.

Ltac pos_tac :=
  match goal with |- ?X = ?Y => 
    assert (tmp: Zpos X = Zpos Y); 
     [idtac; repeat rewrite Zpos_eq_Z_of_nat_o_nat_of_P; eq_tac | injection tmp; auto]
  end; autorewrite with pos_morph.

(**************************************
  Bounded induction
**************************************)

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

