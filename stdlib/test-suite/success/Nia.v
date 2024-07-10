(* -*- coqchk-prog-args: ("-bytecode-compiler" "yes") -*- *)
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Open Scope Z_scope.

(** Add [Z.to_euclidean_division_equations] to the end of [zify], just for this
    file. *)
From Stdlib Require Zify.
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Lemma Z_zerop_or x : x = 0 \/ x <> 0. Proof. apply Z.eq_decidable. Qed.
Lemma Z_eq_dec_or (x y : Z) : x = y \/ x <> y. Proof. apply Z.eq_decidable. Qed.

Ltac with_mod tac :=
  match goal with
  | [ |- context[?x mod ?y] ] => tac x y
  | [ H : context[?x mod ?y] |- _ ] => tac x y
  end.

Ltac with_rem tac :=
  match goal with
  | [ |- context[Z.rem ?x ?y] ] => tac x y
  | [ H : context[Z.rem ?x ?y] |- _ ] => tac x y
  end.

Ltac with_div tac :=
  match goal with
  | [ |- context[?x / ?y] ] => tac x y
  | [ H : context[?x / ?y] |- _ ] => tac x y
  end.

Ltac with_quot tac :=
  match goal with
  | [ |- context[Z.quot ?x ?y] ] => tac x y
  | [ H : context[Z.quot ?x ?y] |- _ ] => tac x y
  end.

Ltac with_mod_rem tac := first [ with_mod tac | with_rem tac ].
Ltac with_div_quot tac := first [ with_div tac | with_quot tac ].
Ltac with_div_mod tac := first [ with_div tac | with_mod tac ].
Ltac with_quot_rem tac := first [ with_quot tac | with_rem tac ].

Ltac pose_eq_fact x y := Z.euclidean_division_equations_pose_eq_fact x y.

Ltac saturate_mod_div_0 :=
  repeat first [ with_mod_rem ltac:(fun x y => pose_eq_fact (x / y) 0)
               | with_div_quot ltac:(fun x y => pose_eq_fact y 0) ].
Ltac saturate_quot_div_0 :=
  repeat first [ with_quot ltac:(fun x y => pose_eq_fact (x ÷ y) 0)
               | with_div ltac:(fun x y => pose_eq_fact (x / y) 0) ].
Ltac saturate_mod_div_eq :=
  let with_the_quot tac := first [ with_div_mod ltac:(fun x y => tac (x / y))
                                 | with_quot_rem ltac:(fun x y => tac (x ÷ y)) ] in
  repeat with_the_quot ltac:(fun q => with_the_quot ltac:(fun q' => pose_eq_fact q q')).

Ltac destr_step :=
  match goal with
  | [ H : and _ _ |- _ ] => destruct H
  | [ H : or _ _ |- _ ] => destruct H
  end.

Ltac t := intros; saturate_mod_div_0; try nia.
Ltac t_zero := intros; saturate_mod_div_0; saturate_quot_div_0; try nia.
(* sometimes this next one is faster? *)
Ltac t_zero_subst := intros; saturate_mod_div_0; saturate_quot_div_0; repeat destr_step; try nia.
Ltac t_eq := intros; saturate_mod_div_eq; try nia.
Ltac t_all := intros; saturate_mod_div_0; saturate_mod_div_eq; try nia.

Example mod_0_l: forall x : Z, 0 mod x = 0. Proof. t. Qed.
Example mod_0_r: forall x : Z, x mod 0 = x. Proof. intros; nia. Qed.
Example Z_mod_same_full: forall a : Z, a mod a = 0. Proof. t. Qed.
Example Zmod_0_l: forall a : Z, 0 mod a = 0. Proof. t. Qed.
Example Zmod_0_r: forall a : Z, a mod 0 = a. Proof. intros; nia. Qed.
Example mod_mod_same: forall x y : Z, (x mod y) mod y = x mod y. Proof. t. Qed.
Example Zmod_mod: forall a n : Z, (a mod n) mod n = a mod n. Proof. t. Qed.
Example Zmod_1_r: forall a : Z, a mod 1 = 0. Proof. intros; nia. Qed.
Example Zmod_div: forall a b : Z, a mod b / b = 0. Proof. intros; nia. Qed.
Example Z_mod_1_r: forall a : Z, a mod 1 = 0. Proof. intros; nia. Qed.
Example Z_mod_same: forall a : Z, a > 0 -> a mod a = 0. Proof. t. Qed.
Example Z_mod_mult: forall a b : Z, (a * b) mod b = 0. Proof. intros; nia. Qed.
Example Z_mod_same': forall a : Z, a <> 0 -> a mod a = 0. Proof. t. Qed.
Example Z_mod_0_l: forall a : Z, a <> 0 -> 0 mod a = 0. Proof. t. Qed.
Example Zmod_opp_opp: forall a b : Z, - a mod - b = - (a mod b). Proof. t_eq. Qed.
Example Z_mod_le: forall a b : Z, 0 <= a -> 0 < b -> a mod b <= a. Proof. t. Qed.
Example Zmod_le: forall a b : Z, 0 < b -> 0 <= a -> a mod b <= a. Proof. t. Qed.
Example Zplus_mod_idemp_r: forall a b n : Z, (b + a mod n) mod n = (b + a) mod n.
Proof.
  intros a b n.
  destruct (Z_zerop n); [ subst; nia | ].
  assert ((b + a mod n) / n = (b / n) + (b mod n + a mod n) / n)
    by nia.
  assert ((b + a) / n = (b / n) + (a / n) + (b mod n + a mod n) / n)
    by nia.
  nia.
Qed.
Example Zplus_mod_idemp_l: forall a b n : Z, (a mod n + b) mod n = (a + b) mod n.
Proof.
  intros a b n.
  destruct (Z_zerop n); [ subst; nia | ].
  assert ((a mod n + b) / n = (b / n) + (b mod n + a mod n) / n) by nia.
  assert ((a + b) / n = (b / n) + (a / n) + (b mod n + a mod n) / n) by nia.
  nia.
Qed.
Example Z_mod_zero_opp_full: forall a b : Z, a mod b = 0 -> - a mod b = 0.
Proof.
  intros a b.
  pose proof (Z_eq_dec_or (a/b) (-(-a/b))).
  nia.
Qed.
Example Zmult_mod_idemp_r: forall a b n : Z, (b * (a mod n)) mod n = (b * a) mod n.
Proof.
  intros a b n.
  destruct (Z_zerop n); [ subst; nia | ].
  assert ((b * (a mod n)) / n = (b / n) * (a mod n) + ((b mod n) * (a mod n)) / n)
    by nia.
  assert ((b * a) / n = (b / n) * (a / n) * n + (b / n) * (a mod n) + (b mod n) * (a / n) + ((b mod n) * (a mod n)) / n)
    by nia.
  nia.
Qed.
Example Zmult_mod_idemp_l: forall a b n : Z, (a mod n * b) mod n = (a * b) mod n.
Proof.
  intros a b n.
  destruct (Z_zerop n); [ subst; nia | ].
  assert (((a mod n) * b) / n = (b / n) * (a mod n) + ((b mod n) * (a mod n)) / n)
    by nia.
  assert ((a * b) / n = (b / n) * (a / n) * n + (b / n) * (a mod n) + (b mod n) * (a / n) + ((b mod n) * (a mod n)) / n)
    by nia.
  nia.
Qed.
Example Zminus_mod_idemp_r: forall a b n : Z, (a - b mod n) mod n = (a - b) mod n.
Proof.
  intros a b n.
  destruct (Z_zerop n); [ subst; nia | ].
  assert ((a - b mod n) / n = a / n + ((a mod n) - (b mod n)) / n) by nia.
  assert ((a - b) / n = a / n - b / n + ((a mod n) - (b mod n)) / n) by nia.
  nia.
Qed.
Example Zminus_mod_idemp_l: forall a b n : Z, (a mod n - b) mod n = (a - b) mod n.
Proof.
  intros a b n.
  destruct (Z_zerop n); [ subst; nia | ].
  assert ((a mod n - b) / n = - (b / n) + ((a mod n) - (b mod n)) / n) by nia.
  assert ((a - b) / n = a / n - b / n + ((a mod n) - (b mod n)) / n) by nia.
  nia.
Qed.
Example Z_mod_plus_full: forall a b c : Z, (a + b * c) mod c = a mod c.
Proof.
  intros a b c.
  pose proof (Z_eq_dec_or ((a+b*c)/c) (a/c + b)).
  nia.
Qed.
Example Z_mod_zero_opp_r: forall a b : Z, a mod b = 0 -> a mod - b = 0.
Proof.
  intros a b.
  pose proof (Z_eq_dec_or (a/b) (-(a/-b))).
  nia.
Qed.
Example Zmod_1_l: forall a : Z, 1 < a -> 1 mod a = 1. Proof. t. Qed.
Example Z_mod_1_l: forall a : Z, 1 < a -> 1 mod a = 1. Proof. t. Qed.
Example Z_mod_mul: forall a b : Z, b <> 0 -> (a * b) mod b = 0. Proof. intros; nia. Qed.
Example Zminus_mod: forall a b n : Z, (a - b) mod n = (a mod n - b mod n) mod n.
Proof.
  intros a b n.
  destruct (Z_zerop n); [ subst; nia | ].
  assert ((a - b) / n = (a / n) - (b / n) + ((a mod n) - (b mod n)) / n) by nia.
  nia.
Qed.
Example Zplus_mod: forall a b n : Z, (a + b) mod n = (a mod n + b mod n) mod n.
Proof.
  intros a b n.
  destruct (Z_zerop n); [ subst; nia | ].
  assert ((a + b) / n = (a / n) + (b / n) + ((a mod n) + (b mod n)) / n) by nia.
  nia.
Qed.
Example Zmult_mod: forall a b n : Z, (a * b) mod n = (a mod n * (b mod n)) mod n.
Proof.
  intros a b n.
  destruct (Z_zerop n); [ subst; nia | ].
  assert ((a * b) / n = n * (a / n) * (b / n) + (a mod n) * (b / n) + (a / n) * (b mod n) + ((a mod n) * (b mod n)) / n)
    by nia.
  nia.
Qed.
Example Z_mod_mod: forall a n : Z, n <> 0 -> (a mod n) mod n = a mod n. Proof. t. Qed.
Example Z_mod_div: forall a b : Z, b <> 0 -> a mod b / b = 0. Proof. intros; nia. Qed.
Example Z_div_exact_full_1: forall a b : Z, a = b * (a / b) -> a mod b = 0. Proof. intros; nia. Qed.
Example Z_mod_pos_bound: forall a b : Z, 0 < b -> 0 <= a mod b < b. Proof. intros; nia. Qed.
Example Z_mod_sign_mul: forall a b : Z, b <> 0 -> 0 <= a mod b * b. Proof. intros; nia. Qed.
Example Z_mod_neg_bound: forall a b : Z, b < 0 -> b < a mod b <= 0. Proof. intros; nia. Qed.
Example Z_mod_neg: forall a b : Z, b < 0 -> b < a mod b <= 0. Proof. intros; nia. Qed.
Example div_mod_small: forall x y : Z, 0 <= x < y -> x mod y = x. Proof. t. Qed.
Example Zmod_small: forall a n : Z, 0 <= a < n -> a mod n = a. Proof. t. Qed.
Example Z_mod_small: forall a b : Z, 0 <= a < b -> a mod b = a. Proof. t. Qed.
Example Z_div_zero_opp_full: forall a b : Z, a mod b = 0 -> - a / b = - (a / b). Proof. intros; nia. Qed.
Example Z_mod_zero_opp: forall a b : Z, b > 0 -> a mod b = 0 -> - a mod b = 0.
Proof.
  intros a b.
  pose proof (Z_eq_dec_or (a/b) (-(-a/b))).
  nia.
Qed.
Example Z_div_zero_opp_r: forall a b : Z, a mod b = 0 -> a / - b = - (a / b). Proof. intros; nia. Qed.
Example Z_mod_lt: forall a b : Z, b > 0 -> 0 <= a mod b < b. Proof. intros; nia. Qed.
Example Z_mod_opp_opp: forall a b : Z, b <> 0 -> - a mod - b = - (a mod b). Proof. t_eq. Qed.
Example Z_mod_bound_pos: forall a b : Z, 0 <= a -> 0 < b -> 0 <= a mod b < b. Proof. intros; nia. Qed.
Example Z_mod_opp_l_z: forall a b : Z, b <> 0 -> a mod b = 0 -> - a mod b = 0.
Proof.
  intros a b.
  pose proof (Z_eq_dec_or (a/b) (-(-a/b))).
  nia.
Qed.
Example Z_mod_plus: forall a b c : Z, c > 0 -> (a + b * c) mod c = a mod c.
Proof.
  intros a b c.
  pose proof (Z_eq_dec_or ((a+b*c)/c) (a/c+b)).
  nia.
Qed.
Example Z_mod_opp_r_z: forall a b : Z, b <> 0 -> a mod b = 0 -> a mod - b = 0.
Proof.
  intros a b.
  pose proof (Z_eq_dec_or (a/b) (-(a/-b))).
  nia.
Qed.
Example Zmod_eq: forall a b : Z, b > 0 -> a mod b = a - a / b * b. Proof. intros; nia. Qed.
Example Z_div_exact_2: forall a b : Z, b > 0 -> a mod b = 0 -> a = b * (a / b). Proof. intros; nia. Qed.
Example Z_div_mod_eq: forall a b : Z, b > 0 -> a = b * (a / b) + a mod b. Proof. intros; nia. Qed.
Example Z_div_exact_1: forall a b : Z, b > 0 -> a = b * (a / b) -> a mod b = 0. Proof. intros; nia. Qed.
Example Z_mod_add: forall a b c : Z, c <> 0 -> (a + b * c) mod c = a mod c.
Proof.
  intros a b c.
  pose proof (Z_eq_dec_or ((a+b*c)/c) (a/c+b)).
  nia.
Qed.
Example Z_mod_nz_opp_r: forall a b : Z, a mod b <> 0 -> a mod - b = a mod b - b.
Proof.
  intros a b.
  assert (b <> 0 -> a mod b <> 0 -> a / -b = -(a/b)-1) by t.
  nia.
Qed.
Example Z_mul_mod_idemp_l: forall a b n : Z, n <> 0 -> (a mod n * b) mod n = (a * b) mod n.
Proof.
  intros a b n ?.
  assert (((a mod n) * b) / n = (b / n) * (a mod n) + ((b mod n) * (a mod n)) / n)
    by nia.
  assert ((a * b) / n = (b / n) * (a / n) * n + (b / n) * (a mod n) + (b mod n) * (a / n) + ((b mod n) * (a mod n)) / n)
    by nia.
  nia.
Qed.
Example Z_mod_nz_opp_full: forall a b : Z, a mod b <> 0 -> - a mod b = b - a mod b.
Proof.
  intros a b.
  assert (b <> 0 -> a mod b <> 0 -> -a/b = -1-a/b) by nia.
  nia.
Qed.
Example Z_add_mod_idemp_r: forall a b n : Z, n <> 0 -> (a + b mod n) mod n = (a + b) mod n.
Proof.
  intros a b n ?.
  assert ((a + b mod n) / n = (a / n) + (a mod n + b mod n) / n) by nia.
  assert ((a + b) / n = (a / n) + (b / n) + (a mod n + b mod n) / n) by nia.
  nia.
Qed.
Example Z_add_mod_idemp_l: forall a b n : Z, n <> 0 -> (a mod n + b) mod n = (a + b) mod n.
Proof.
  intros a b n ?.
  assert ((a mod n + b) / n = (b / n) + (a mod n + b mod n) / n) by nia.
  assert ((a + b) / n = (a / n) + (b / n) + (a mod n + b mod n) / n) by nia.
  nia.
Qed.
Example Z_mul_mod_idemp_r: forall a b n : Z, n <> 0 -> (a * (b mod n)) mod n = (a * b) mod n.
Proof.
  intros a b n ?.
  assert ((a * (b mod n)) / n = (a / n) * (b mod n) + ((a mod n) * (b mod n)) / n)
    by nia.
  assert ((a * b) / n = (b / n) * (a / n) * n + (b / n) * (a mod n) + (b mod n) * (a / n) + ((a mod n) * (b mod n)) / n)
    by nia.
  nia.
Qed.
Example Zmod_eq_full: forall a b : Z, b <> 0 -> a mod b = a - a / b * b. Proof. intros; nia. Qed.
Example div_eq: forall x y : Z, y <> 0 -> x mod y = 0 -> x / y * y = x. Proof. intros; nia. Qed.
Example Z_mod_eq: forall a b : Z, b <> 0 -> a mod b = a - b * (a / b). Proof. intros; nia. Qed.
Example Z_mod_sign_nz: forall a b : Z, b <> 0 -> a mod b <> 0 -> Z.sgn (a mod b) = Z.sgn b. Proof. intros; nia. Qed.
Example Z_div_exact_full_2: forall a b : Z, b <> 0 -> a mod b = 0 -> a = b * (a / b). Proof. intros; nia. Qed.
Example Z_div_mod: forall a b : Z, b <> 0 -> a = b * (a / b) + a mod b. Proof. intros; nia. Qed.
Example Z_add_mod: forall a b n : Z, n <> 0 -> (a + b) mod n = (a mod n + b mod n) mod n.
Proof.
  intros a b n ?.
  assert ((a + b) / n = (a / n) + (b / n) + (a mod n + b mod n) / n) by nia.
  nia.
Qed.
Example Z_mul_mod: forall a b n : Z, n <> 0 -> (a * b) mod n = (a mod n * (b mod n)) mod n.
Proof.
  intros a b n ?.
  assert ((a * b) / n = (b / n) * (a / n) * n + (b / n) * (a mod n) + (b mod n) * (a / n) + ((a mod n) * (b mod n)) / n)
    by nia.
  nia.
Qed.
Example Z_div_exact: forall a b : Z, b <> 0 -> a = b * (a / b) <-> a mod b = 0. Proof. intros; nia. Qed.
Example Z_div_opp_l_z: forall a b : Z, b <> 0 -> a mod b = 0 -> - a / b = - (a / b). Proof. intros; nia. Qed.
Example Z_div_opp_r_z: forall a b : Z, b <> 0 -> a mod b = 0 -> a / - b = - (a / b). Proof. intros; nia. Qed.
Example Z_mod_opp_r_nz: forall a b : Z, b <> 0 -> a mod b <> 0 -> a mod - b = a mod b - b.
Proof.
  intros a b.
  assert (b <> 0 -> a mod b <> 0 -> a/(-b) = -1-a/b) by nia.
  nia.
Qed.
Example Z_mod_opp_l_nz: forall a b : Z, b <> 0 -> a mod b <> 0 -> - a mod b = b - a mod b.
Proof.
  intros a b.
  assert (b <> 0 -> a mod b <> 0 -> -a/b = -1-a/b) by nia.
  nia.
Qed.
Example mod_eq: forall x x' y : Z, x / y = x' / y -> x mod y = x' mod y -> y <> 0 -> x = x'. Proof. intros; nia. Qed.
Example Z_div_nz_opp_r: forall a b : Z, b <> 0 -> a mod b <> 0 -> a / - b = - (a / b) - 1. Proof. intros; nia. Qed.
Example Z_div_nz_opp_full: forall a b : Z, b <> 0 -> a mod b <> 0 -> - a / b = - (a / b) - 1. Proof. intros; nia. Qed.
Example Zmod_unique: forall a b q r : Z, 0 <= r < b -> a = b * q + r -> r = a mod b. Proof. intros; nia. Qed.
Example Z_mod_unique_neg: forall a b q r : Z, b < r <= 0 -> a = b * q + r -> r = a mod b. Proof. intros; nia. Qed.
Example Z_mod_unique_pos: forall a b q r : Z, 0 <= r < b -> a = b * q + r -> r = a mod b. Proof. intros; nia. Qed.
Example Z_mod_bound_or: forall a b : Z, b <> 0 -> 0 <= a mod b < b \/ b < a mod b <= 0. Proof. intros; nia. Qed.
Example Z_div_opp_l_nz: forall a b : Z, b <> 0 -> a mod b <> 0 -> - a / b = - (a / b) - 1. Proof. intros; nia. Qed.
Example Z_div_opp_r_nz: forall a b : Z, b <> 0 -> a mod b <> 0 -> a / - b = - (a / b) - 1. Proof. intros; nia. Qed.
Example Z_mod_small_iff: forall a b : Z, b <> 0 -> a mod b = a <-> 0 <= a < b \/ b < a <= 0. Proof. t. Qed.
Example Z_mod_unique: forall a b q r : Z, 0 <= r < b \/ b < r <= 0 -> a = b * q + r -> r = a mod b. Proof. intros. nia. Qed.
Example Z_opp_mod_bound_or: forall a b : Z, b <> 0 -> 0 <= - (a mod b) < - b \/ - b < - (a mod b) <= 0. Proof. intros; nia. Qed.

Example Zdiv_0_r: forall a : Z, a / 0 = 0. Proof. intros; nia. Qed.
Example Zdiv_0_l: forall a : Z, 0 / a = 0. Proof. intros; nia. Qed.
Example Z_div_1_r: forall a : Z, a / 1 = a. Proof. intros; nia. Qed.
Example Zdiv_1_r: forall a : Z, a / 1 = a. Proof. intros; nia. Qed.
Example Zdiv_opp_opp: forall a b : Z, - a / - b = a / b. Proof. intros; nia. Qed.
Example Z_div_0_l: forall a : Z, a <> 0 -> 0 / a = 0. Proof. intros; nia. Qed.
Example Z_div_pos: forall a b : Z, b > 0 -> 0 <= a -> 0 <= a / b. Proof. intros; nia. Qed.
Example Z_div_ge0: forall a b : Z, b > 0 -> a >= 0 -> a / b >= 0. Proof. intros; nia. Qed.
Example Z_div_pos': forall a b : Z, 0 <= a -> 0 < b -> 0 <= a / b. Proof. intros; nia. Qed.
Example Z_mult_div_ge: forall a b : Z, b > 0 -> b * (a / b) <= a. Proof. intros; nia. Qed.
Example Z_mult_div_ge_neg: forall a b : Z, b < 0 -> b * (a / b) >= a. Proof. intros; nia. Qed.
Example Z_mul_div_le: forall a b : Z, 0 < b -> b * (a / b) <= a. Proof. intros; nia. Qed.
Example Z_mul_div_ge: forall a b : Z, b < 0 -> a <= b * (a / b). Proof. intros; nia. Qed.
Example Z_div_same: forall a : Z, a > 0 -> a / a = 1. Proof. intros; nia. Qed.
Example Z_div_mult: forall a b : Z, b > 0 -> a * b / b = a. Proof. intros; nia. Qed.
Example Z_mul_succ_div_gt: forall a b : Z, 0 < b -> a < b * Z.succ (a / b). Proof. intros; nia. Qed.
Example Z_mul_succ_div_lt: forall a b : Z, b < 0 -> b * Z.succ (a / b) < a. Proof. intros; nia. Qed.
Example Zdiv_1_l: forall a : Z, 1 < a -> 1 / a = 0. Proof. intros; nia. Qed.
Example Z_div_1_l: forall a : Z, 1 < a -> 1 / a = 0. Proof. intros; nia. Qed.
Example Z_div_str_pos: forall a b : Z, 0 < b <= a -> 0 < a / b. Proof. intros; nia. Qed.
Example Z_div_ge: forall a b c : Z, c > 0 -> a >= b -> a / c >= b / c. Proof. intros; nia. Qed.
Example Z_div_mult_full: forall a b : Z, b <> 0 -> a * b / b = a. Proof. intros; nia. Qed.
Example Z_div_same': forall a : Z, a <> 0 -> a / a = 1. Proof. intros; nia. Qed.
Example Zdiv_lt_upper_bound: forall a b q : Z, 0 < b -> a < q * b -> a / b < q. Proof. intros; nia. Qed.
Example Z_div_mul: forall a b : Z, b <> 0 -> a * b / b = a. Proof. intros; nia. Qed.
Example Z_div_lt: forall a b : Z, 0 < a -> 1 < b -> a / b < a. Proof. intros; nia. Qed.
Example Z_div_le_mono: forall a b c : Z, 0 < c -> a <= b -> a / c <= b / c. Proof. intros; nia. Qed.
Example Zdiv_sgn: forall a b : Z, 0 <= Z.sgn (a / b) * Z.sgn a * Z.sgn b. Proof. intros; nia. Qed.
Example Z_div_same_full: forall a : Z, a <> 0 -> a / a = 1. Proof. intros; nia. Qed.
Example Z_div_lt_upper_bound: forall a b q : Z, 0 < b -> a < b * q -> a / b < q. Proof. intros; nia. Qed.
Example Z_div_le: forall a b c : Z, c > 0 -> a <= b -> a / c <= b / c. Proof. intros; nia. Qed.
Example Z_div_le_lower_bound: forall a b q : Z, 0 < b -> b * q <= a -> q <= a / b. Proof. intros; nia. Qed.
Example Zdiv_le_lower_bound: forall a b q : Z, 0 < b -> q * b <= a -> q <= a / b. Proof. intros; nia. Qed.
Example Zdiv_le_upper_bound: forall a b q : Z, 0 < b -> a <= q * b -> a / b <= q. Proof. intros; nia. Qed.
Example Z_div_le_upper_bound: forall a b q : Z, 0 < b -> a <= b * q -> a / b <= q. Proof. intros; nia. Qed.
Example Z_div_small: forall a b : Z, 0 <= a < b -> a / b = 0. Proof. intros; nia. Qed.
Example Zdiv_small: forall a b : Z, 0 <= a < b -> a / b = 0. Proof. intros; nia. Qed.
Example Z_div_opp_opp: forall a b : Z, b <> 0 -> - a / - b = a / b. Proof. intros; nia. Qed.
Example Z_div_unique_exact: forall a b q : Z, b <> 0 -> a = b * q -> q = a / b. Proof. intros; nia. Qed.
Example Zdiv_le_compat_l: forall p q r : Z, 0 <= p -> 0 < q < r -> p / r <= p / q.
Proof.
  intros p q r ??.
  assert (p mod r <= p mod q \/ p mod q <= p mod r) by nia.
  assert (0 <= p / r) by nia.
  assert (0 <= p / q) by nia.
  nia.
Qed.
Example Z_div_le_compat_l: forall p q r : Z, 0 <= p -> 0 < q <= r -> p / r <= p / q.
Proof.
  intros p q r ??.
  assert (p mod r <= p mod q \/ p mod q <= p mod r) by nia.
  assert (0 <= p / r) by nia.
  assert (0 <= p / q) by nia.
  nia.
Qed.
Example Z_div_plus: forall a b c : Z, c > 0 -> (a + b * c) / c = a / c + b. Proof. intros; nia. Qed.
Example Z_div_lt': forall a b : Z, b >= 2 -> a > 0 -> a / b < a. Proof. intros; nia. Qed.
Example Zdiv_mult_le: forall a b c : Z, 0 <= a -> 0 <= b -> 0 <= c -> c * (a / b) <= c * a / b. Proof. intros; nia. Qed.
Example Z_div_add_l: forall a b c : Z, b <> 0 -> (a * b + c) / b = a + c / b. Proof. intros; nia. Qed.
Example Z_div_plus_full_l: forall a b c : Z, b <> 0 -> (a * b + c) / b = a + c / b. Proof. intros; nia. Qed.
Example Z_div_add: forall a b c : Z, c <> 0 -> (a + b * c) / c = a / c + b. Proof. intros; nia. Qed.
Example Z_div_plus_full: forall a b c : Z, c <> 0 -> (a + b * c) / c = a / c + b. Proof. intros; nia. Qed.
Example Z_div_mul_le: forall a b c : Z, 0 <= a -> 0 < b -> 0 <= c -> c * (a / b) <= c * a / b. Proof. intros; nia. Qed.
Example Z_div_mul_cancel_r: forall a b c : Z, b <> 0 -> c <> 0 -> a * c / (b * c) = a / b. Proof. intros; nia. Qed.
Example Z_div_div: forall a b c : Z, b <> 0 -> 0 < c -> a / b / c = a / (b * c). Proof. intros; nia. Qed.
Example Z_div_mul_cancel_l: forall a b c : Z, b <> 0 -> c <> 0 -> c * a / (c * b) = a / b. Proof. intros; nia. Qed.
Example Z_div_unique_neg: forall a b q r : Z, b < r <= 0 -> a = b * q + r -> q = a / b. Proof. intros; nia. Qed.
Example Zdiv_unique: forall a b q r : Z, 0 <= r < b -> a = b * q + r -> q = a / b. Proof. intros; nia. Qed.
Example Z_div_unique_pos: forall a b q r : Z, 0 <= r < b -> a = b * q + r -> q = a / b. Proof. intros; nia. Qed.
Example Z_div_small_iff: forall a b : Z, b <> 0 -> a / b = 0 <-> 0 <= a < b \/ b < a <= 0. Proof. intros; nia. Qed.
Example Z_div_unique: forall a b q r : Z, 0 <= r < b \/ b < r <= 0 -> a = b * q + r -> q = a / b. Proof. intros; nia. Qed.
Example Z_divide_mod : forall a b : Z, (b | a) -> a mod b = 0. Proof. intros. nia. Qed.
Example Z_mod_divide: forall a b : Z, b <> 0 -> a mod b = 0 <-> (b | a). Proof. split; intros. Fail all: nia. Abort.
Example Zmod_divides: forall a b : Z, b <> 0 -> a mod b = 0 <-> (exists c : Z, a = b * c). Proof. split; intros. Fail all: nia. Abort.

(** Now we do the same, but with [Z.quot] and [Z.rem] instead. *)
Example N2Z_inj_quot : forall n m : N, Z.of_N (n / m) = Z.of_N n ÷ Z.of_N m. Proof. intros; nia. Qed.
Example N2Z_inj_rem : forall n m : N, Z.of_N (n mod m) = Z.rem (Z.of_N n) (Z.of_N m). Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_mul_quot_ge : forall a b : Z, a <= 0 -> b <> 0 -> a <= b * (a ÷ b) <= 0. Proof. t_zero. Qed.
Example OrdersEx_Z_as_DT_mul_quot_le : forall a b : Z, 0 <= a -> b <> 0 -> 0 <= b * (a ÷ b) <= a. Proof. t_zero. Qed.
Example OrdersEx_Z_as_DT_Private_Div_NZQuot_div_0_l : forall a : Z, 0 < a -> 0 ÷ a = 0. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_Private_Div_NZQuot_div_1_l : forall a : Z, 1 < a -> 1 ÷ a = 0. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_Private_Div_NZQuot_div_1_r : forall a : Z, 0 <= a -> a ÷ 1 = a. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_Private_Div_NZQuot_div_add : forall a b c : Z, 0 <= a -> 0 <= a + b * c -> 0 < c -> (a + b * c) ÷ c = a ÷ c + b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_Private_Div_NZQuot_div_add_l : forall a b c : Z, 0 <= c -> 0 <= a * b + c -> 0 < b -> (a * b + c) ÷ b = a + c ÷ b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_Private_Div_NZQuot_div_div : forall a b c : Z, 0 <= a -> 0 < b -> 0 < c -> a ÷ b ÷ c = a ÷ (b * c).
Proof. intros; assert (0 < b * c) by nia; nia. Qed.
Example OrdersEx_Z_as_DT_Private_Div_NZQuot_div_le_lower_bound : forall a b q : Z, 0 <= a -> 0 < b -> b * q <= a -> q <= a ÷ b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_Private_Div_NZQuot_div_le_mono : forall a b c : Z, 0 < c -> 0 <= a <= b -> a ÷ c <= b ÷ c. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_Private_Div_NZQuot_div_le_upper_bound : forall a b q : Z, 0 <= a -> 0 < b -> a <= b * q -> a ÷ b <= q. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_Private_Div_NZQuot_div_lt : forall a b : Z, 0 < a -> 1 < b -> a ÷ b < a. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_Private_Div_NZQuot_div_lt_upper_bound : forall a b q : Z, 0 <= a -> 0 < b -> a < b * q -> a ÷ b < q. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_Private_Div_NZQuot_div_mul : forall a b : Z, 0 <= a -> 0 < b -> a * b ÷ b = a. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_Private_Div_NZQuot_div_mul_le : forall a b c : Z, 0 <= a -> 0 < b -> 0 <= c -> c * (a ÷ b) <= c * a ÷ b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_Private_Div_NZQuot_div_pos : forall a b : Z, 0 <= a -> 0 < b -> 0 <= a ÷ b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_Private_Div_NZQuot_div_same : forall a : Z, 0 < a -> a ÷ a = 1. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_Private_Div_NZQuot_div_small : forall a b : Z, 0 <= a < b -> a ÷ b = 0. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_Private_Div_NZQuot_div_small_iff : forall a b : Z, 0 <= a -> 0 < b -> a ÷ b = 0 <-> a < b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_Private_Div_NZQuot_div_str_pos : forall a b : Z, 0 < b <= a -> 0 < a ÷ b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_Private_Div_NZQuot_div_str_pos_iff : forall a b : Z, 0 <= a -> 0 < b -> 0 < a ÷ b <-> b <= a. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_Private_Div_NZQuot_div_unique_exact : forall a b q : Z, 0 <= a -> 0 < b -> a = b * q -> q = a ÷ b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_Private_Div_NZQuot_mul_div_le : forall a b : Z, 0 <= a -> 0 < b -> b * (a ÷ b) <= a. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_quot_0_l : forall a : Z, a <> 0 -> 0 ÷ a = 0. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_quot_1_l : forall a : Z, 1 < a -> 1 ÷ a = 0. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_quot_1_r : forall a : Z, a ÷ 1 = a. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_quot_div_nonneg : forall a b : Z, 0 <= a -> 0 < b -> a ÷ b = a / b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_quot_le_lower_bound : forall a b q : Z, 0 < b -> b * q <= a -> q <= a ÷ b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_quot_le_mono : forall a b c : Z, 0 < c -> a <= b -> a ÷ c <= b ÷ c. Proof. t_zero. Qed.
Example OrdersEx_Z_as_DT_quot_le_upper_bound : forall a b q : Z, 0 < b -> a <= b * q -> a ÷ b <= q. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_quot_lt : forall a b : Z, 0 < a -> 1 < b -> a ÷ b < a. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_quot_lt_upper_bound : forall a b q : Z, 0 <= a -> 0 < b -> a < b * q -> a ÷ b < q. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_quot_mul : forall a b : Z, b <> 0 -> a * b ÷ b = a. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_quot_mul_le : forall a b c : Z, 0 <= a -> 0 < b -> 0 <= c -> c * (a ÷ b) <= c * a ÷ b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_quot_pos : forall a b : Z, 0 <= a -> 0 < b -> 0 <= a ÷ b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_quot_same : forall a : Z, a <> 0 -> a ÷ a = 1. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_quot_small : forall a b : Z, 0 <= a < b -> a ÷ b = 0. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_quot_str_pos : forall a b : Z, 0 < b <= a -> 0 < a ÷ b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_quot_unique_exact : forall a b q : Z, b <> 0 -> a = b * q -> q = a ÷ b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_DT_quot_unique : forall a b q r : Z, 0 <= a -> 0 <= r < b -> a = b * q + r -> q = a ÷ b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_mul_quot_ge : forall a b : Z, a <= 0 -> b <> 0 -> a <= b * (a ÷ b) <= 0.
Proof.
  intros.
  assert (0 < a ÷ b \/ a ÷ b = 0 \/ a ÷ b < 0) by nia.
  nia.
Qed.
Example OrdersEx_Z_as_OT_mul_quot_le : forall a b : Z, 0 <= a -> b <> 0 -> 0 <= b * (a ÷ b) <= a.
Proof.
  intros.
  assert (0 < a ÷ b \/ a ÷ b = 0 \/ a ÷ b < 0) by nia.
  nia.
Qed.
Example OrdersEx_Z_as_OT_Private_Div_NZQuot_div_0_l : forall a : Z, 0 < a -> 0 ÷ a = 0. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_Private_Div_NZQuot_div_1_l : forall a : Z, 1 < a -> 1 ÷ a = 0. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_Private_Div_NZQuot_div_1_r : forall a : Z, 0 <= a -> a ÷ 1 = a. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_Private_Div_NZQuot_div_add : forall a b c : Z, 0 <= a -> 0 <= a + b * c -> 0 < c -> (a + b * c) ÷ c = a ÷ c + b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_Private_Div_NZQuot_div_add_l : forall a b c : Z, 0 <= c -> 0 <= a * b + c -> 0 < b -> (a * b + c) ÷ b = a + c ÷ b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_Private_Div_NZQuot_div_le_lower_bound : forall a b q : Z, 0 <= a -> 0 < b -> b * q <= a -> q <= a ÷ b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_Private_Div_NZQuot_div_le_mono : forall a b c : Z, 0 < c -> 0 <= a <= b -> a ÷ c <= b ÷ c. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_Private_Div_NZQuot_div_le_upper_bound : forall a b q : Z, 0 <= a -> 0 < b -> a <= b * q -> a ÷ b <= q. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_Private_Div_NZQuot_div_lt : forall a b : Z, 0 < a -> 1 < b -> a ÷ b < a. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_Private_Div_NZQuot_div_lt_upper_bound : forall a b q : Z, 0 <= a -> 0 < b -> a < b * q -> a ÷ b < q. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_Private_Div_NZQuot_div_mul_cancel_l : forall a b c : Z, 0 <= a -> 0 < b -> 0 < c -> c * a ÷ (c * b) = a ÷ b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_Private_Div_NZQuot_div_mul_cancel_r : forall a b c : Z, 0 <= a -> 0 < b -> 0 < c -> a * c ÷ (b * c) = a ÷ b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_Private_Div_NZQuot_div_mul : forall a b : Z, 0 <= a -> 0 < b -> a * b ÷ b = a. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_Private_Div_NZQuot_div_mul_le : forall a b c : Z, 0 <= a -> 0 < b -> 0 <= c -> c * (a ÷ b) <= c * a ÷ b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_Private_Div_NZQuot_div_pos : forall a b : Z, 0 <= a -> 0 < b -> 0 <= a ÷ b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_Private_Div_NZQuot_div_same : forall a : Z, 0 < a -> a ÷ a = 1. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_Private_Div_NZQuot_div_small : forall a b : Z, 0 <= a < b -> a ÷ b = 0. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_Private_Div_NZQuot_div_small_iff : forall a b : Z, 0 <= a -> 0 < b -> a ÷ b = 0 <-> a < b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_Private_Div_NZQuot_div_str_pos : forall a b : Z, 0 < b <= a -> 0 < a ÷ b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_Private_Div_NZQuot_div_str_pos_iff : forall a b : Z, 0 <= a -> 0 < b -> 0 < a ÷ b <-> b <= a. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_Private_Div_NZQuot_div_unique_exact : forall a b q : Z, 0 <= a -> 0 < b -> a = b * q -> q = a ÷ b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_Private_Div_NZQuot_div_unique : forall a b q r : Z, 0 <= a -> 0 <= r < b -> a = b * q + r -> q = a ÷ b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_Private_Div_NZQuot_mul_div_le : forall a b : Z, 0 <= a -> 0 < b -> b * (a ÷ b) <= a. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_quot_0_l : forall a : Z, a <> 0 -> 0 ÷ a = 0. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_quot_1_l : forall a : Z, 1 < a -> 1 ÷ a = 0. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_quot_1_r : forall a : Z, a ÷ 1 = a. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_quot_div_nonneg : forall a b : Z, 0 <= a -> 0 < b -> a ÷ b = a / b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_quot_le_lower_bound : forall a b q : Z, 0 < b -> b * q <= a -> q <= a ÷ b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_quot_le_mono : forall a b c : Z, 0 < c -> a <= b -> a ÷ c <= b ÷ c. Proof. t_zero. Qed.
Example OrdersEx_Z_as_OT_quot_le_upper_bound : forall a b q : Z, 0 < b -> a <= b * q -> a ÷ b <= q. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_quot_lt : forall a b : Z, 0 < a -> 1 < b -> a ÷ b < a. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_quot_lt_upper_bound : forall a b q : Z, 0 <= a -> 0 < b -> a < b * q -> a ÷ b < q. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_quot_mul : forall a b : Z, b <> 0 -> a * b ÷ b = a. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_quot_mul_le : forall a b c : Z, 0 <= a -> 0 < b -> 0 <= c -> c * (a ÷ b) <= c * a ÷ b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_quot_opp_l : forall a b : Z, b <> 0 -> - a ÷ b = - (a ÷ b). Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_quot_pos : forall a b : Z, 0 <= a -> 0 < b -> 0 <= a ÷ b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_quot_same : forall a : Z, a <> 0 -> a ÷ a = 1. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_quot_small : forall a b : Z, 0 <= a < b -> a ÷ b = 0. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_quot_str_pos : forall a b : Z, 0 < b <= a -> 0 < a ÷ b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_quot_unique_exact : forall a b q : Z, b <> 0 -> a = b * q -> q = a ÷ b. Proof. intros; nia. Qed.
Example OrdersEx_Z_as_OT_quot_unique : forall a b q r : Z, 0 <= a -> 0 <= r < b -> a = b * q + r -> q = a ÷ b. Proof. intros; nia. Qed.
Example Z2N_inj_rem : forall n m : Z, 0 <= n -> 0 <= m -> Z.to_N (Z.rem n m) = (Z.to_N n mod Z.to_N m)%N. Proof. intros. Abort.
Example Zabs2N_inj_rem : forall n m : Z, Z.abs_N (Z.rem n m) = (Z.abs_N n mod Z.abs_N m)%N. Proof. intros. Abort.
Example Z_add_rem_idemp_l : forall a b n : Z, n <> 0 -> 0 <= a * b -> Z.rem (Z.rem a n + b) n = Z.rem (a + b) n. Proof. intros. Fail nia. Abort.
Example Z_add_rem_idemp_r : forall a b n : Z, n <> 0 -> 0 <= a * b -> Z.rem (a + Z.rem b n) n = Z.rem (a + b) n. Proof. intros. Fail nia. Abort.
Example Z_gcd_quot_gcd : forall a b g : Z, g <> 0 -> g = Z.gcd a b -> Z.gcd (a ÷ g) (b ÷ g) = 1. Proof. intros. Fail nia. Abort.
Example Z_gcd_rem : forall a b : Z, b <> 0 -> Z.gcd (Z.rem a b) b = Z.gcd b a. Proof. intros. Fail nia. Abort.
Example Z_mul_pred_quot_gt : forall a b : Z, 0 <= a -> b < 0 -> a < b * Z.pred (a ÷ b). Proof. intros; nia. Qed.
Example Z_mul_pred_quot_lt : forall a b : Z, a <= 0 -> 0 < b -> b * Z.pred (a ÷ b) < a. Proof. intros; nia. Qed.
Example Z_mul_quot_ge : forall a b : Z, a <= 0 -> b <> 0 -> a <= b * (a ÷ b) <= 0. Proof. intros. Fail nia. Abort.
Example Z_mul_quot_le : forall a b : Z, 0 <= a -> b <> 0 -> 0 <= b * (a ÷ b) <= a. Proof. intros. Fail nia. Abort.
Example Z_mul_rem_distr_l : forall a b c : Z, b <> 0 -> c <> 0 -> Z.rem (c * a) (c * b) = c * Z.rem a b. Proof. intros. Fail nia. Abort.
Example Z_mul_rem_distr_r : forall a b c : Z, b <> 0 -> c <> 0 -> Z.rem (a * c) (b * c) = Z.rem a b * c. Proof. intros. Fail nia. Abort.
Example Z_mul_rem_idemp_l : forall a b n : Z, n <> 0 -> Z.rem (Z.rem a n * b) n = Z.rem (a * b) n. Proof. intros. Fail nia. Abort.
Example Z_mul_rem_idemp_r : forall a b n : Z, n <> 0 -> Z.rem (a * Z.rem b n) n = Z.rem (a * b) n. Proof. intros. Fail nia. Abort.
Example Z_mul_succ_quot_gt : forall a b : Z, 0 <= a -> 0 < b -> a < b * Z.succ (a ÷ b). Proof. intros; nia. Qed.
Example Z_mul_succ_quot_lt : forall a b : Z, a <= 0 -> b < 0 -> b * Z.succ (a ÷ b) < a. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_add_mod : forall a b n : Z, 0 <= a -> 0 <= b -> 0 < n -> Z.rem (a + b) n = Z.rem (Z.rem a n + Z.rem b n) n. Proof. intros. Fail nia. Abort.
Example Z_Private_Div_NZQuot_add_mod_idemp_l : forall a b n : Z, 0 <= a -> 0 <= b -> 0 < n -> Z.rem (Z.rem a n + b) n = Z.rem (a + b) n. Proof. intros. Fail nia. Abort.
Example Z_Private_Div_NZQuot_add_mod_idemp_r : forall a b n : Z, 0 <= a -> 0 <= b -> 0 < n -> Z.rem (a + Z.rem b n) n = Z.rem (a + b) n. Proof. intros. Fail nia. Abort.
Example Z_Private_Div_NZQuot_div_0_l : forall a : Z, 0 < a -> 0 ÷ a = 0. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_div_1_l : forall a : Z, 1 < a -> 1 ÷ a = 0. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_div_1_r : forall a : Z, 0 <= a -> a ÷ 1 = a. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_div_add : forall a b c : Z, 0 <= a -> 0 <= a + b * c -> 0 < c -> (a + b * c) ÷ c = a ÷ c + b. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_div_add_l : forall a b c : Z, 0 <= c -> 0 <= a * b + c -> 0 < b -> (a * b + c) ÷ b = a + c ÷ b. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_div_exact : forall a b : Z, 0 <= a -> 0 < b -> a = b * (a ÷ b) <-> Z.rem a b = 0. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_div_le_lower_bound : forall a b q : Z, 0 <= a -> 0 < b -> b * q <= a -> q <= a ÷ b. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_div_le_mono : forall a b c : Z, 0 < c -> 0 <= a <= b -> a ÷ c <= b ÷ c. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_div_le_upper_bound : forall a b q : Z, 0 <= a -> 0 < b -> a <= b * q -> a ÷ b <= q. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_div_lt : forall a b : Z, 0 < a -> 1 < b -> a ÷ b < a. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_div_lt_upper_bound : forall a b q : Z, 0 <= a -> 0 < b -> a < b * q -> a ÷ b < q. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_div_mul_cancel_l : forall a b c : Z, 0 <= a -> 0 < b -> 0 < c -> c * a ÷ (c * b) = a ÷ b. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_div_mul_cancel_r : forall a b c : Z, 0 <= a -> 0 < b -> 0 < c -> a * c ÷ (b * c) = a ÷ b. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_div_mul : forall a b : Z, 0 <= a -> 0 < b -> a * b ÷ b = a. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_div_mul_le : forall a b c : Z, 0 <= a -> 0 < b -> 0 <= c -> c * (a ÷ b) <= c * a ÷ b. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_div_pos : forall a b : Z, 0 <= a -> 0 < b -> 0 <= a ÷ b. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_div_same : forall a : Z, 0 < a -> a ÷ a = 1. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_div_small : forall a b : Z, 0 <= a < b -> a ÷ b = 0. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_div_small_iff : forall a b : Z, 0 <= a -> 0 < b -> a ÷ b = 0 <-> a < b. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_div_str_pos : forall a b : Z, 0 < b <= a -> 0 < a ÷ b. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_div_str_pos_iff : forall a b : Z, 0 <= a -> 0 < b -> 0 < a ÷ b <-> b <= a. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_div_unique_exact : forall a b q : Z, 0 <= a -> 0 < b -> a = b * q -> q = a ÷ b. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_div_unique : forall a b q r : Z, 0 <= a -> 0 <= r < b -> a = b * q + r -> q = a ÷ b. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_mod_0_l : forall a : Z, 0 < a -> Z.rem 0 a = 0. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_mod_1_l : forall a : Z, 1 < a -> Z.rem 1 a = 1. Proof. intros. Fail nia. Abort.
Example Z_Private_Div_NZQuot_mod_1_r : forall a : Z, 0 <= a -> Z.rem a 1 = 0. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_mod_add : forall a b c : Z, 0 <= a -> 0 <= a + b * c -> 0 < c -> Z.rem (a + b * c) c = Z.rem a c. Proof. intros. Fail nia. Abort.
Example Z_Private_Div_NZQuot_mod_divides : forall a b : Z, 0 <= a -> 0 < b -> Z.rem a b = 0 <-> (exists c : Z, a = b * c). Proof. intros. Fail nia. Abort.
Example Z_Private_Div_NZQuot_mod_le : forall a b : Z, 0 <= a -> 0 < b -> Z.rem a b <= a. Proof. intros. Fail nia. Abort.
Example Z_Private_Div_NZQuot_mod_mod : forall a n : Z, 0 <= a -> 0 < n -> Z.rem (Z.rem a n) n = Z.rem a n. Proof. intros. Fail nia. Abort.
Example Z_Private_Div_NZQuot_mod_mul : forall a b : Z, 0 <= a -> 0 < b -> Z.rem (a * b) b = 0. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_mod_mul_r : forall a b c : Z, 0 <= a -> 0 < b -> 0 < c -> Z.rem a (b * c) = Z.rem a b + b * Z.rem (a ÷ b) c. Proof. intros. Fail nia. Abort.
Example Z_Private_Div_NZQuot_mod_same : forall a : Z, 0 < a -> Z.rem a a = 0. Proof. intros. Fail nia. Abort.
Example Z_Private_Div_NZQuot_mod_small : forall a b : Z, 0 <= a < b -> Z.rem a b = a. Proof. intros. Fail nia. Abort.
Example Z_Private_Div_NZQuot_mod_small_iff : forall a b : Z, 0 <= a -> 0 < b -> Z.rem a b = a <-> a < b. Proof. intros. Fail nia. Abort.
Example Z_Private_Div_NZQuot_mul_div_le : forall a b : Z, 0 <= a -> 0 < b -> b * (a ÷ b) <= a. Proof. intros; nia. Qed.
Example Z_Private_Div_NZQuot_mul_mod_distr_l : forall a b c : Z, 0 <= a -> 0 < b -> 0 < c -> Z.rem (c * a) (c * b) = c * Z.rem a b. Proof. intros. Fail nia. Abort.
Example Z_Private_Div_NZQuot_mul_mod_distr_r : forall a b c : Z, 0 <= a -> 0 < b -> 0 < c -> Z.rem (a * c) (b * c) = Z.rem a b * c. Proof. intros. Fail nia. Abort.
Example Z_Private_Div_NZQuot_mul_mod_idemp_l : forall a b n : Z, 0 <= a -> 0 <= b -> 0 < n -> Z.rem (Z.rem a n * b) n = Z.rem (a * b) n. Proof. intros. Fail nia. Abort.
Example Z_Private_Div_NZQuot_mul_mod_idemp_r : forall a b n : Z, 0 <= a -> 0 <= b -> 0 < n -> Z.rem (a * Z.rem b n) n = Z.rem (a * b) n. Proof. intros. Fail nia. Abort.
Example Z_Private_Div_NZQuot_mul_succ_div_gt : forall a b : Z, 0 <= a -> 0 < b -> a < b * Z.succ (a ÷ b). Proof. intros; nia. Qed.
Example Z_Private_Div_Quot2Div_div_mod : forall a b : Z, b <> 0 -> a = b * (a ÷ b) + Z.rem a b. Proof. intros; nia. Qed.
Example Z_Private_Div_Quot2Div_div_wd : Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Z.quot. Proof. repeat intro; subst; nia. Qed.
Example Z_Private_Div_Quot2Div_mod_bound_pos : forall a b : Z, 0 <= a -> 0 < b -> 0 <= Z.rem a b < b. Proof. intros; nia. Qed.
Example Z_Private_Div_Quot2Div_mod_wd : Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Z.rem. Proof. repeat intro; subst; nia. Qed.
Example Z_quot_0_l : forall a : Z, a <> 0 -> 0 ÷ a = 0. Proof. intros; nia. Qed.
Example Z_quot_0_r_ext : forall x y : Z, y = 0 -> x ÷ y = 0. Proof. intros; nia. Qed.
Example Z_quot_1_l : forall a : Z, 1 < a -> 1 ÷ a = 0. Proof. intros; nia. Qed.
Example Z_quot_1_r : forall a : Z, a ÷ 1 = a. Proof. intros; nia. Qed.
Example Zquot2_quot : forall n : Z, Z.quot2 n = n ÷ 2. Proof. intros; nia. Qed.
Example Z_quot_div_nonneg : forall a b : Z, 0 <= a -> 0 < b -> a ÷ b = a / b. Proof. intros; nia. Qed.
Example Z_quot_exact : forall a b : Z, b <> 0 -> a = b * (a ÷ b) <-> Z.rem a b = 0. Proof. intros; nia. Qed.
Example Z_quot_le_compat_l : forall p q r : Z, 0 <= p -> 0 < q <= r -> p ÷ r <= p ÷ q. Proof. intros. Fail nia. Abort.
Example Z_quot_le_lower_bound : forall a b q : Z, 0 < b -> b * q <= a -> q <= a ÷ b. Proof. intros; nia. Qed.
Example Z_quot_le_mono : forall a b c : Z, 0 < c -> a <= b -> a ÷ c <= b ÷ c. Proof. intros. Fail nia. Abort.
Example Z_quot_le_upper_bound : forall a b q : Z, 0 < b -> a <= b * q -> a ÷ b <= q. Proof. intros; nia. Qed.
Example Z_quot_lt : forall a b : Z, 0 < a -> 1 < b -> a ÷ b < a. Proof. intros; nia. Qed.
Example Z_quot_lt_upper_bound : forall a b q : Z, 0 <= a -> 0 < b -> a < b * q -> a ÷ b < q. Proof. intros; nia. Qed.
Example Z_quot_mul : forall a b : Z, b <> 0 -> a * b ÷ b = a. Proof. intros; nia. Qed.
Example Z_quot_mul_le : forall a b c : Z, 0 <= a -> 0 < b -> 0 <= c -> c * (a ÷ b) <= c * a ÷ b. Proof. intros; nia. Qed.
Example Z_quot_opp_l : forall a b : Z, b <> 0 -> - a ÷ b = - (a ÷ b). Proof. intros; nia. Qed.
Example Z_quot_pos : forall a b : Z, 0 <= a -> 0 < b -> 0 <= a ÷ b. Proof. intros; nia. Qed.
Example Z_quot_rem' : forall a b : Z, a = b * (a ÷ b) + Z.rem a b. Proof. intros; nia. Qed.
Example Z_quot_rem : forall a b : Z, b <> 0 -> a = b * (a ÷ b) + Z.rem a b. Proof. intros; nia. Qed.
Example Z_quot_same : forall a : Z, a <> 0 -> a ÷ a = 1. Proof. intros; nia. Qed.
Example Z_quot_small : forall a b : Z, 0 <= a < b -> a ÷ b = 0. Proof. intros; nia. Qed.
Example Z_quot_small_iff : forall a b : Z, b <> 0 -> a ÷ b = 0 <-> Z.abs a < Z.abs b. Proof. intros; nia. Qed.
Example Z_quot_str_pos : forall a b : Z, 0 < b <= a -> 0 < a ÷ b. Proof. intros; nia. Qed.
Example Z_quot_unique_exact : forall a b q : Z, b <> 0 -> a = b * q -> q = a ÷ b. Proof. intros; nia. Qed.
Example Z_quot_unique : forall a b q r : Z, 0 <= a -> 0 <= r < b -> a = b * q + r -> q = a ÷ b. Proof. intros; nia. Qed.
Example Z_quot_wd : Morphisms.Proper (Morphisms.respectful Z.eq (Morphisms.respectful Z.eq Z.eq)) Z.quot. Proof. repeat intro. Fail nia. Abort.
Example Zquot_Zeven_rem : forall a : Z, Z.even a = (Z.rem a 2 =? 0). Proof. intros. Fail nia. Abort.
Example Zquot_Z_mult_quot_ge : forall a b : Z, a <= 0 -> a <= b * (a ÷ b) <= 0. Proof. intros. Fail nia. Abort.
Example Zquot_Z_mult_quot_le : forall a b : Z, 0 <= a -> 0 <= b * (a ÷ b) <= a. Proof. intros. Fail nia. Abort.
Example Zquot_Zodd_rem : forall a : Z, Z.odd a = negb (Z.rem a 2 =? 0). Proof. intros. Fail nia. Abort.
Example Zquot_Zplus_rem : forall a b n : Z, 0 <= a * b -> Z.rem (a + b) n = Z.rem (Z.rem a n + Z.rem b n) n. Proof. intros. Abort.
Example Zquot_Zplus_rem_idemp_l : forall a b n : Z, 0 <= a * b -> Z.rem (Z.rem a n + b) n = Z.rem (a + b) n. Proof. intros. Abort.
Example Zquot_Zplus_rem_idemp_r : forall a b n : Z, 0 <= a * b -> Z.rem (b + Z.rem a n) n = Z.rem (b + a) n. Proof. intros. Abort.
Example Zquot_Zquot_0_l : forall a : Z, 0 ÷ a = 0. Proof. intros; nia. Qed.
Example Zquot_Zquot_0_r : forall a : Z, a ÷ 0 = 0. Proof. intros; nia. Qed.
Example Zquot_Z_quot_exact_full : forall a b : Z, a = b * (a ÷ b) <-> Z.rem a b = 0. Proof. intros; nia. Qed.
Example Zquot_Zquot_le_lower_bound : forall a b q : Z, 0 < b -> q * b <= a -> q <= a ÷ b. Proof. intros; nia. Qed.
Example Zquot_Zquot_le_upper_bound : forall a b q : Z, 0 < b -> a <= q * b -> a ÷ b <= q. Proof. intros; nia. Qed.
Example Zquot_Z_quot_lt : forall a b : Z, 0 < a -> 2 <= b -> a ÷ b < a. Proof. intros; nia. Qed.
Example Zquot_Zquot_lt_upper_bound : forall a b q : Z, 0 <= a -> 0 < b -> a < q * b -> a ÷ b < q. Proof. intros; nia. Qed.
From Stdlib Require Zquot.
Example Zquot_Zquot_mod_unique_full : forall a b q r : Z, Zquot.Remainder a b r -> a = b * q + r -> q = a ÷ b /\ r = Z.rem a b. Proof. intros. Fail nia. Abort.
Example Zquot_Z_quot_monotone : forall a b c : Z, 0 <= c -> a <= b -> a ÷ c <= b ÷ c. Proof. intros. Fail nia. Abort.
Example Zquot_Zquot_mult_cancel_l : forall a b c : Z, c <> 0 -> c * a ÷ (c * b) = a ÷ b. Proof. intros. Abort.
Example Zquot_Zquot_mult_cancel_r : forall a b c : Z, c <> 0 -> a * c ÷ (b * c) = a ÷ b. Proof. intros. Abort.
Example Zquot_Zquot_mult_le : forall a b c : Z, 0 <= a -> 0 <= b -> 0 <= c -> c * (a ÷ b) <= c * a ÷ b. Proof. intros; nia. Qed.
Example Zquot_Z_quot_pos : forall a b : Z, 0 <= a -> 0 <= b -> 0 <= a ÷ b. Proof. intros; nia. Qed.
Example Zquot_Zquotrem_Zdiv_eucl_pos : forall a b : Z, 0 <= a -> 0 < b -> a ÷ b = a / b /\ Z.rem a b = a mod b. Proof. intros; nia. Qed.
Example Zquot_Zquot_sgn : forall a b : Z, 0 <= Z.sgn (a ÷ b) * Z.sgn a * Z.sgn b. Proof. intros; nia. Qed.
Example Zquot_Zquot_unique_full : forall a b q r : Z, Zquot.Remainder a b r -> a = b * q + r -> q = a ÷ b. Proof. intros. Fail nia. Abort.
Example Zquot_Zquot_Zdiv_pos : forall a b : Z, 0 <= a -> 0 <= b -> a ÷ b = a / b. Proof. intros; nia. Qed.
Example Zquot_Zquot_Zquot : forall a b c : Z, a ÷ b ÷ c = a ÷ (b * c). Proof. intros. Abort.
Example Zquot_Zrem_0_l : forall a : Z, Z.rem 0 a = 0. Proof. intros; nia. Qed.
Example Zquot_Zrem_0_r : forall a : Z, Z.rem a 0 = a. Proof. intros; nia. Qed.
Example Zquot_Zrem_divides : forall a b : Z, Z.rem a b = 0 <-> (exists c : Z, a = b * c). Proof. intros. Fail nia. Abort.
Example Zquot_Zrem_even : forall a : Z, Z.rem a 2 = (if Z.even a then 0 else Z.sgn a). Proof. intros. Fail nia. Abort.
Example Zquot_Zrem_le : forall a b : Z, 0 <= a -> 0 <= b -> Z.rem a b <= a. Proof. intros. Fail nia. Abort.
Example Zquot_Zrem_lt_neg : forall a b : Z, a <= 0 -> b <> 0 -> - Z.abs b < Z.rem a b <= 0. Proof. intros; nia. Qed.
Example Zquot_Zrem_lt_neg_neg : forall a b : Z, a <= 0 -> b < 0 -> b < Z.rem a b <= 0. Proof. intros; nia. Qed.
Example Zquot_Zrem_lt_neg_pos : forall a b : Z, a <= 0 -> 0 < b -> - b < Z.rem a b <= 0. Proof. intros; nia. Qed.
Example Zquot_Zrem_lt_pos : forall a b : Z, 0 <= a -> b <> 0 -> 0 <= Z.rem a b < Z.abs b. Proof. intros; nia. Qed.
Example Zquot_Zrem_lt_pos_neg : forall a b : Z, 0 <= a -> b < 0 -> 0 <= Z.rem a b < - b. Proof. intros; nia. Qed.
Example Zquot_Zrem_lt_pos_pos : forall a b : Z, 0 <= a -> 0 < b -> 0 <= Z.rem a b < b. Proof. intros; nia. Qed.
Example Zquot_Z_rem_mult : forall a b : Z, Z.rem (a * b) b = 0. Proof. intros; nia. Qed.
Example Zquot_Zrem_odd : forall a : Z, Z.rem a 2 = (if Z.odd a then Z.sgn a else 0). Proof. intros. Fail nia. Abort.
Example Zquot_Zrem_opp_l : forall a b : Z, Z.rem (- a) b = - Z.rem a b. Proof. intros. Fail nia. Abort.
Example Zquot_Zrem_opp_opp : forall a b : Z, Z.rem (- a) (- b) = - Z.rem a b. Proof. intros. Fail nia. Abort.
Example Zquot_Zrem_opp_r : forall a b : Z, Z.rem a (- b) = Z.rem a b. Proof. intros. Fail nia. Abort.
Example Zquot_Z_rem_plus : forall a b c : Z, 0 <= (a + b * c) * a -> Z.rem (a + b * c) c = Z.rem a c. Proof. intros. Fail nia. Abort.
Example Zquot_Zrem_rem : forall a n : Z, Z.rem (Z.rem a n) n = Z.rem a n. Proof. intros. Fail nia. Abort.
Example Zquot_Z_rem_same : forall a : Z, Z.rem a a = 0. Proof. intros. Fail nia. Abort.
Example Zquot_Zrem_sgn2 : forall a b : Z, 0 <= Z.rem a b * a. Proof. intros. Fail nia. Abort.
Example Zquot_Zrem_sgn : forall a b : Z, 0 <= Z.sgn (Z.rem a b) * Z.sgn a. Proof. intros; nia. Qed.
Example Zquot_Zrem_unique_full : forall a b q r : Z, Zquot.Remainder a b r -> a = b * q + r -> r = Z.rem a b. Proof. intros. Fail nia. Abort.
Example Zquot_Zrem_Zmod_pos : forall a b : Z, 0 <= a -> 0 < b -> Z.rem a b = a mod b. Proof. intros; nia. Qed.
Example Zquot_Zrem_Zmod_zero : forall a b : Z, b <> 0 -> Z.rem a b = 0 <-> a mod b = 0. Proof. intros; nia. Qed.
Example Z_rem_0_l : forall a : Z, a <> 0 -> Z.rem 0 a = 0. Proof. intros; nia. Qed.
Example Z_rem_0_r_ext : forall x y : Z, y = 0 -> Z.rem x y = x. Proof. intros; nia. Qed.
Example Z_rem_1_l : forall a : Z, 1 < a -> Z.rem 1 a = 1. Proof. intros. Fail nia. Abort.
Example Z_rem_1_r : forall a : Z, Z.rem a 1 = 0. Proof. intros; nia. Qed.
Example Z_rem_abs : forall a b : Z, b <> 0 -> Z.rem (Z.abs a) (Z.abs b) = Z.abs (Z.rem a b). Proof. intros. Fail nia. Abort.
Example Z_rem_abs_l : forall a b : Z, b <> 0 -> Z.rem (Z.abs a) b = Z.abs (Z.rem a b). Proof. intros. Fail nia. Abort.
Example Z_rem_abs_r : forall a b : Z, b <> 0 -> Z.rem a (Z.abs b) = Z.rem a b. Proof. intros. Fail nia. Abort.
Example Z_rem_add : forall a b c : Z, c <> 0 -> 0 <= (a + b * c) * a -> Z.rem (a + b * c) c = Z.rem a c. Proof. intros. Fail nia. Abort.
Example Z_rem_bound_abs : forall a b : Z, b <> 0 -> Z.abs (Z.rem a b) < Z.abs b. Proof. intros; nia. Qed.
Example Z_rem_bound_neg_neg : forall x y : Z, y < 0 -> x <= 0 -> y < Z.rem x y <= 0. Proof. intros; nia. Qed.
Example Z_rem_bound_neg_pos : forall x y : Z, y < 0 -> 0 <= x -> 0 <= Z.rem x y < - y. Proof. intros; nia. Qed.
Example Z_rem_bound_pos : forall a b : Z, 0 <= a -> 0 < b -> 0 <= Z.rem a b < b. Proof. intros; nia. Qed.
Example Z_rem_bound_pos_neg : forall x y : Z, 0 < y -> x <= 0 -> - y < Z.rem x y <= 0. Proof. intros; nia. Qed.
Example Z_rem_bound_pos_pos : forall x y : Z, 0 < y -> 0 <= x -> 0 <= Z.rem x y < y. Proof. intros; nia. Qed.
Example Z_rem_eq : forall a b : Z, b <> 0 -> Z.rem a b = a - b * (a ÷ b). Proof. intros; nia. Qed.
Example Z_rem_le : forall a b : Z, 0 <= a -> 0 < b -> Z.rem a b <= a. Proof. intros. Fail nia. Abort.
Example Z_rem_mod_eq_0 : forall a b : Z, b <> 0 -> Z.rem a b = 0 <-> a mod b = 0. Proof. intros; nia. Qed.
Example Z_rem_mod : forall a b : Z, b <> 0 -> Z.rem a b = Z.sgn a * (Z.abs a mod Z.abs b). Proof. intros. Fail nia. Abort.
Example Z_rem_mod_nonneg : forall a b : Z, 0 <= a -> 0 < b -> Z.rem a b = a mod b. Proof. intros; nia. Qed.
Example Z_rem_mul : forall a b : Z, b <> 0 -> Z.rem (a * b) b = 0. Proof. intros; nia. Qed.
Example Z_rem_nonneg : forall a b : Z, b <> 0 -> 0 <= a -> 0 <= Z.rem a b. Proof. intros; nia. Qed.
Example Z_rem_nonpos : forall a b : Z, b <> 0 -> a <= 0 -> Z.rem a b <= 0. Proof. intros; nia. Qed.
Example Z_rem_opp_l : forall a b : Z, b <> 0 -> Z.rem (- a) b = - Z.rem a b. Proof. intros. Fail nia. Abort.
Example Z_rem_opp_l' : forall a b : Z, Z.rem (- a) b = - Z.rem a b. Proof. intros. Fail nia. Abort.
Example Z_rem_opp_opp : forall a b : Z, b <> 0 -> Z.rem (- a) (- b) = - Z.rem a b. Proof. intros. Fail nia. Abort.
Example Z_rem_opp_r : forall a b : Z, b <> 0 -> Z.rem a (- b) = Z.rem a b. Proof. intros. Fail nia. Abort.
Example Z_rem_opp_r' : forall a b : Z, Z.rem a (- b) = Z.rem a b. Proof. intros. Fail nia. Abort.
Example Z_rem_quot : forall a b : Z, b <> 0 -> Z.rem a b ÷ b = 0. Proof. intros; nia. Qed.
Example Z_rem_rem : forall a n : Z, n <> 0 -> Z.rem (Z.rem a n) n = Z.rem a n. Proof. intros. Fail nia. Abort.
Example Z_rem_same : forall a : Z, a <> 0 -> Z.rem a a = 0. Proof. intros. Fail nia. Abort.
Example Z_rem_sign : forall a b : Z, a <> 0 -> b <> 0 -> Z.sgn (Z.rem a b) <> - Z.sgn a. Proof. intros; nia. Qed.
Example Z_rem_sign_mul : forall a b : Z, b <> 0 -> 0 <= Z.rem a b * a. Proof. intros. Fail nia. Abort.
Example Z_rem_sign_nz : forall a b : Z, b <> 0 -> Z.rem a b <> 0 -> Z.sgn (Z.rem a b) = Z.sgn a. Proof. intros; nia. Qed.
Example Z_rem_small : forall a b : Z, 0 <= a < b -> Z.rem a b = a. Proof. intros. Fail nia. Abort.
Example Z_rem_small_iff : forall a b : Z, b <> 0 -> Z.rem a b = a <-> Z.abs a < Z.abs b. Proof. intros. Fail nia. Abort.
Example Z_rem_unique : forall a b q r : Z, 0 <= a -> 0 <= r < b -> a = b * q + r -> r = Z.rem a b. Proof. intros; nia. Qed.
Example Z_rem_divide: forall a b : Z, b <> 0 -> Z.rem a b = 0 <-> (b | a). Proof. split; intros. Fail all: nia. Abort.
Example Zrem_divides: forall a b : Z, b <> 0 -> Z.rem a b = 0 <-> (exists c : Z, a = b * c). Proof. split; intros. Fail all: nia. Abort.
Example Z_rem_wd : Morphisms.Proper (Morphisms.respectful Z.eq (Morphisms.respectful Z.eq Z.eq)) Z.rem. Proof. repeat intro; subst. Fail nia. Abort.
