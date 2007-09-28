
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

(**********************************************************************
     ZDivModAux.v                                                              
                                                                               
     Auxillary functions & Theorems for Zdiv and Zmod                          
 **********************************************************************)

Require Export ZArith.
Require Export Znumtheory.
Require Export Tactic.
Require Import ZAux.
Require Import ZPowerAux.

Open Local Scope Z_scope. 

Hint  Extern 2 (Zle _ _) => 
 (match goal with
  |- Zpos _ <= Zpos _ => exact (refl_equal _)
  | H: _ <=  ?p |- _ <= ?p => apply Zle_trans with (2 := H)
  | H: _ <  ?p |- _ <= ?p => 
   apply Zlt_le_weak; apply Zle_lt_trans with (2 := H)
  end).

Hint  Extern 2 (Zlt _ _) => 
 (match goal with
   |- Zpos _ < Zpos _ => exact (refl_equal _)
|      H: _ <=  ?p |- _ <= ?p => apply Zlt_le_trans with (2 := H)
|   H: _ <  ?p |- _ <= ?p => apply Zle_lt_trans with (2 := H)
  end).

Hint Resolve Zlt_gt Zle_ge: zarith.

(************************************** 
  Properties Zmod 
**************************************)
 
 Theorem Zmod_mult:
   forall a b n, 0 < n ->  (a * b) mod n = ((a mod n) * (b mod n)) mod n.
 Proof.
  intros a b n H.
  pattern a at 1; rewrite (Z_div_mod_eq a n); auto with zarith.
  pattern b at 1; rewrite (Z_div_mod_eq b n); auto with zarith.
  replace ((n * (a / n) + a mod n) * (n * (b / n) + b mod n)) with
   ((a mod n) * (b mod n) +
   (((n*(a/n)) * (b/n) + (b mod n)*(a / n)) + (a mod n) * (b / n)) * n);
   auto with zarith.
  apply Z_mod_plus; auto with zarith.
  ring.
 Qed.

 Theorem Zmod_plus:
    forall a b n, 0 < n ->  (a + b) mod n = (a mod n + b mod n) mod n.
 Proof.
  intros a b n H.
  pattern a at 1; rewrite (Z_div_mod_eq a n); auto with zarith.
  pattern b at 1; rewrite (Z_div_mod_eq b n); auto with zarith.
  replace ((n * (a / n) + a mod n) + (n * (b / n) + b mod n))
     with ((a mod n + b mod n) + (a / n + b / n) * n); auto with zarith.
  apply Z_mod_plus; auto with zarith.
  ring.
 Qed.
 
 Theorem Zmod_mod: forall a n, 0 < n -> (a mod n) mod n = a mod n.
 Proof.
  intros a n H.
  pattern a at 2; rewrite (Z_div_mod_eq a n); auto with zarith.
  rewrite Zplus_comm; rewrite Zmult_comm.
  apply sym_equal; apply Z_mod_plus; auto with zarith.
 Qed.
 
 Theorem Zmod_def_small: forall a n, 0 <= a < n  ->  a mod n = a.
 Proof.
  intros a n [H1 H2]; unfold Zmod.
  generalize (Z_div_mod a n); case (Zdiv_eucl a n).
  intros q r H3; case H3; clear H3; auto with zarith.
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

 Theorem Zmod_minus: 
     forall a b n, 0 < n -> (a - b) mod n = (a mod n - b mod n) mod n.
 Proof.
  intros a b n H; replace (a - b) with (a + (-1) * b); auto with zarith.
  replace (a mod n - b mod n) with (a mod n + (-1)*(b mod n));auto with zarith.
  rewrite Zmod_plus; auto with zarith.
  rewrite Zmod_mult; auto with zarith.
  rewrite (fun x y => Zmod_plus x  ((-1) * y)); auto with zarith.
  rewrite Zmod_mult; auto with zarith.
  rewrite (fun x => Zmod_mult x (b mod n)); auto with zarith.
  repeat rewrite Zmod_mod; auto.
 Qed.

 Theorem Zmod_le: forall a n, 0 < n -> 0 <= a -> (Zmod a n) <= a.
 Proof.
  intros a n H1 H2; case (Zle_or_lt n  a); intros H3.
  case (Z_mod_lt a n); auto with zarith.
  rewrite Zmod_def_small; auto with zarith.
 Qed.

 Theorem Zmod_le_first: forall a b, 0 <= a -> 0 < b -> 0 <= a mod b <= a.
 Proof.
  intros a b H H1;case (Z_mod_lt a b);auto with zarith;intros H2 H3;split;auto.
  case (Zle_or_lt b a); intros H4; auto with zarith.
  rewrite Zmod_def_small; auto with zarith.
 Qed.


(**************************************
 Properties of Zdivide
**************************************)
 
 Theorem Zdiv_pos: forall a b, 0 < b -> 0 <= a -> 0 <= a / b.
 Proof.
  intros; apply Zge_le; apply Z_div_ge0; auto with zarith.
 Qed. 
 Hint Resolve Zdiv_pos: zarith.

 Theorem Zdiv_mult_le:
   forall a b c, 0 <= a -> 0 < b -> 0 <= c -> c * (a/b) <= (c * a)/ b.
 Proof.
  intros a b c H1 H2 H3.
  case (Z_mod_lt a b); auto with zarith; intros Hu1 Hu2.
  case (Z_mod_lt c b); auto with zarith; intros Hv1 Hv2.
  apply Zmult_le_reg_r with b; auto with zarith.
  rewrite <- Zmult_assoc.
  replace (a / b * b) with (a - a mod b).
  replace (c * a / b * b) with (c * a - (c * a) mod b).
  rewrite Zmult_minus_distr_l.
  unfold Zminus; apply Zplus_le_compat_l.
  match goal with |- - ?X <= -?Y => assert (Y <= X); auto with zarith end.
  apply Zle_trans with ((c mod b) * (a mod b)); auto with zarith.
  rewrite Zmod_mult; case (Zmod_le_first ((c mod b) * (a mod b)) b); 
    auto with zarith.
  apply Zmult_le_compat_r; auto with zarith.
  case (Zmod_le_first c b); auto.
  pattern (c * a) at 1; rewrite (Z_div_mod_eq (c * a) b); try ring; 
    auto with zarith.
  pattern a at 1; rewrite (Z_div_mod_eq a b); try ring; auto with zarith.
 Qed.

 Theorem Zdiv_unique:
   forall n d q r, 0 < d -> ( 0 <= r < d ) -> n = d * q + r ->  q = n / d.
 Proof.
  intros n d q r H H0 H1.
  assert (H2: n = d * (n / d) + n mod d).
  apply Z_div_mod_eq; auto with zarith.
  assert (H3:  0 <= n mod d < d ).
  apply Z_mod_lt; auto with zarith.
  case (Ztrichotomy q (n / d)); auto.
  intros H4.
  absurd (n < n); auto with zarith.
  pattern n at 1; rewrite H1; rewrite H2.
  apply Zlt_le_trans with (d * (q + 1)); auto with zarith.
  rewrite Zmult_plus_distr_r; auto with zarith.
  apply Zle_trans with (d * (n / d)); auto with zarith.
  intros tmp; case tmp; auto; intros H4; clear tmp.
  absurd (n < n); auto with zarith.
  pattern n at 2; rewrite H1; rewrite H2.
  apply Zlt_le_trans with (d * (n / d + 1)); auto with zarith.
  rewrite Zmult_plus_distr_r; auto with zarith.
  apply Zle_trans with (d * q); auto with zarith.
 Qed.

 Theorem Zmod_unique:
   forall n d q r, 0 < d -> ( 0 <= r < d ) -> n = d * q + r ->  r = n mod d.
 Proof.
  intros n d q r H H0 H1.
  assert (H2: n = d * (n / d) + n mod d).
  apply Z_div_mod_eq; auto with zarith.
  rewrite (Zdiv_unique n d q r) in H1; auto.
  apply (Zplus_reg_l (d * (n / d))); auto with zarith.
 Qed.

 Theorem Zmod_Zmult_compat_l: forall a b c, 
   0 < b -> 0 < c -> c * a  mod (c * b) = c * (a mod b).
 Proof.
  intros a b c H2 H3.
  pattern a at 1; rewrite (Z_div_mod_eq a b); auto with zarith.
  rewrite Zplus_comm; rewrite Zmult_plus_distr_r.
  rewrite Zmult_assoc; rewrite (Zmult_comm (c * b)).
  rewrite Z_mod_plus; auto with zarith.
  apply Zmod_def_small; split; auto with zarith.
  apply Zmult_le_0_compat; auto with zarith.
  destruct (Z_mod_lt a b);auto with zarith.
  apply Zmult_lt_compat_l; auto with zarith.
  destruct (Z_mod_lt a b);auto with zarith.
 Qed.

 Theorem Zdiv_Zmult_compat_l: 
   forall a b c, 0 <= a -> 0 < b -> 0 < c -> c * a / (c * b) = a / b.
 Proof.
  intros a b c H1 H2 H3; case (Z_mod_lt a b); auto with zarith; intros H4 H5.
  apply Zdiv_unique with (a mod b); auto with zarith.
  apply Zmult_reg_l with c; auto with zarith.
  rewrite Zmult_plus_distr_r; rewrite <- Zmod_Zmult_compat_l; auto with zarith.
  rewrite Zmult_assoc; apply Z_div_mod_eq; auto with zarith.
 Qed.

 Theorem Zdiv_0: forall a, 0 < a -> 0 / a = 0.
 Proof.
  intros a H;apply sym_equal;apply Zdiv_unique with (r := 0); auto with zarith.
 Qed.

 Theorem Zdiv_le_upper_bound: 
   forall a b q, 0 <= a -> 0 < b -> a <= q * b -> a / b <= q.
 Proof.
  intros a b q H1 H2 H3.
  apply Zmult_le_reg_r with b; auto with zarith.
  apply Zle_trans with (2 := H3).
  pattern a at 2; rewrite (Z_div_mod_eq a b); auto with zarith.
  rewrite (Zmult_comm b); case (Z_mod_lt a b); auto with zarith.
 Qed.

 Theorem Zdiv_lt_upper_bound: 
   forall a b q, 0 <= a -> 0 < b -> a < q * b -> a / b < q.
 Proof.
  intros a b q H1 H2 H3.
  apply Zmult_lt_reg_r with b; auto with zarith.
  apply Zle_lt_trans with (2 := H3).
  pattern a at 2; rewrite (Z_div_mod_eq a b); auto with zarith.
  rewrite (Zmult_comm b); case (Z_mod_lt a b); auto with zarith.
 Qed.

 Theorem Zdiv_le_lower_bound: 
   forall a b q, 0 <= a -> 0 < b -> q * b <= a -> q <= a / b.
 Proof.
  intros a b q H1 H2 H3.
  assert (q < a / b + 1); auto with zarith.
  apply Zmult_lt_reg_r with b; auto with zarith.
  apply Zle_lt_trans with (1 := H3).
  pattern a at 1; rewrite (Z_div_mod_eq a b); auto with zarith.
  rewrite Zmult_plus_distr_l; rewrite (Zmult_comm b); case (Z_mod_lt a b);
   auto with zarith.
 Qed.

 Theorem Zmult_mod_distr_l: 
   forall a b c, 0 < a -> 0 < c -> (a * b) mod (a * c) = a * (b mod c).
 Proof.
  intros a b c H Hc.
  apply sym_equal; apply Zmod_unique with (b / c); auto with zarith.
  apply Zmult_lt_0_compat; auto.
  case (Z_mod_lt b c); auto with zarith; intros; split; auto with zarith.
  apply Zmult_lt_compat_l; auto.
  rewrite <- Zmult_assoc; rewrite <- Zmult_plus_distr_r.
  rewrite <- Z_div_mod_eq; auto with zarith.
 Qed.


 Theorem Zmod_distr: forall a b r t, 0 <= a <= b -> 0 <= r -> 0 <= t < 2 ^a ->
  (2 ^a * r + t) mod (2 ^ b) = (2 ^a * r) mod (2 ^ b) + t.
 Proof.
  intros a b r t (H1, H2) H3 (H4, H5).
  assert (t < 2 ^ b).
  apply Zlt_le_trans with (1:= H5); auto with zarith.
  apply Zpower_le_monotone; auto with zarith.
  rewrite Zmod_plus; auto with zarith.
  rewrite Zmod_def_small with (a := t); auto with zarith.
  apply Zmod_def_small; auto with zarith.
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

 Theorem Zmult_mod_distr_r:
   forall a b c : Z, 0 < a -> 0 < c -> (b * a) mod (c * a) = (b mod c) * a.
 Proof.
  intros; repeat rewrite (fun x => (Zmult_comm x a)).
  apply Zmult_mod_distr_l; auto.
 Qed.

 Theorem Z_div_plus_l: forall a b c : Z, 0 < b -> (a * b + c) / b = a  + c / b.
 Proof.
  intros a b c H; rewrite Zplus_comm; rewrite Z_div_plus;
   try apply Zplus_comm; auto with zarith. 
 Qed.

 Theorem Zmod_shift_r:
   forall a b r t, 0 <= a <= b -> 0 <= r -> 0 <= t < 2 ^a ->
     (r * 2 ^a + t) mod (2 ^ b) = (r * 2 ^a) mod (2 ^ b) + t.
 Proof.
  intros a b r t (H1, H2) H3 (H4, H5).
  assert (t < 2 ^ b).
  apply Zlt_le_trans with (1:= H5); auto with zarith.
  apply Zpower_le_monotone; auto with zarith.
  rewrite Zmod_plus; auto with zarith.
  rewrite Zmod_def_small with (a := t); auto with zarith.
  apply Zmod_def_small; auto with zarith.
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

  Theorem Zdiv_lt_0: forall a b, 0 <= a < b -> a / b = 0.
  intros a b H; apply sym_equal; apply Zdiv_unique with a; auto with zarith.
  Qed.

  Theorem Zmod_mult_0: forall a b, 0 < b  -> (a * b) mod b = 0.
  Proof.
   intros a b H; rewrite <- (Zplus_0_l (a * b)); rewrite Z_mod_plus;
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
   rewrite (Zmult_comm (2 ^ b)); rewrite Z_div_plus_l; auto with zarith.
   rewrite (fun x y => @Zdiv_lt_0 (x mod y)); auto with zarith.
   match goal with |- context [?X mod ?Y] => case (Z_mod_lt X Y) end; 
    auto with zarith.
  Qed.


  Theorem Zpos_minus: 
     forall a b, Zpos a < Zpos b -> Zpos (b- a) = Zpos b - Zpos a.
  Proof.
   intros a b H.
   repeat rewrite Zpos_eq_Z_of_nat_o_nat_of_P; autorewrite with pos_morph;
     auto with zarith.
   rewrite inj_minus1; auto with zarith.
   match goal with |- (?X <= ?Y)%nat =>
    case (le_or_lt X Y); auto; intro tmp; absurd (Z_of_nat X < Z_of_nat Y); 
        try apply Zle_not_lt; auto with zarith
    end.
   repeat rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P; auto with zarith.
   generalize (Zlt_gt _ _ H); auto.
 Qed.

  Theorem Zdiv_Zmult_compat_r:
     forall a b c : Z, 0 <= a -> 0 < b -> 0 < c -> a * c / (b * c) = a / b.
  Proof.
   intros a b c H H1 H2; repeat rewrite (fun x => Zmult_comm x c); 
    apply Zdiv_Zmult_compat_l; auto.
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
  symmetry;apply Zdiv_Zmult_compat_r.
  destruct H1;trivial.
  apply Zpower_lt_0;auto with zarith.
  apply Zpower_lt_0;auto with zarith.
  rewrite <- Zpower_exp.
  replace (n-p+p) with n;trivial. ring.
  omega. omega.
  apply Zlt_gt. apply Zpower_lt_0;auto with zarith.
 Qed.

 Lemma Zdiv_Zdiv : forall a b c, 0 < b -> 0 < c -> (a/b)/c = a / (b*c).
 Proof.
  intros a b c H H0.
  pattern a at 2;rewrite (Z_div_mod_eq a b);auto with zarith.
  pattern (a/b) at 2;rewrite (Z_div_mod_eq (a/b) c);auto with zarith.
  replace (b * (c * (a / b / c) + (a / b) mod c) + a mod b) with
    ((a / b / c)*(b * c)  + (b * ((a / b) mod c) + a mod b));try ring.
  rewrite Z_div_plus_l;auto with zarith.
  rewrite (Zdiv_lt_0 (b * ((a / b) mod c) + a mod b)).
  ring.
  split.
  apply Zplus_le_0_compat;auto with zarith.
  apply Zmult_le_0_compat;auto with zarith.
  destruct (Z_mod_lt (a/b) c);auto with zarith.
  destruct (Z_mod_lt a b);auto with zarith.
  apply Zle_lt_trans with (b * ((a / b) mod c) + (b-1)).
  destruct (Z_mod_lt a b);auto with zarith.
  apply Zle_lt_trans with (b * (c-1) + (b - 1)).
  apply Zplus_le_compat;auto with zarith.
  destruct (Z_mod_lt (a/b) c);auto with zarith.
  replace (b * (c - 1) + (b - 1)) with (b*c-1);try ring;auto with zarith.
  apply Zmult_lt_0_compat;auto with zarith.
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
 
