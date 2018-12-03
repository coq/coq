Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Ltac cleanup :=
  repeat match goal with
         | [ H : ?T -> _, H' : ?T |- _ ] => specialize (H H')
         | [ H : ?T -> _, H' : ~?T |- _ ] => clear H
         | [ H : ~?T -> _, H' : ?T |- _ ] => clear H
         | [ H : 0 < ?x -> _, H' : ?x < 0 |- _ ] => clear H
         | [ H : ?x < 0 -> _, H' : 0 < ?x |- _ ] => clear H
         | _ => progress subst
         end.

(** Add [Z.div_mod_to_quot_rem] to the end of [zify], just for this
    file.  Note that we also add a [cleanup] tactic, which is very
    important for speed purposes. *)
Ltac zify ::= repeat (zify_nat; zify_positive; zify_N); zify_op; Z.div_mod_to_quot_rem; cleanup.

Lemma Z_zerop_or x : x = 0 \/ x <> 0. Proof. nia. Qed.
Lemma Z_eq_dec_or (x y : Z) : x = y \/ x <> y. Proof. nia. Qed.

Ltac unique_pose_proof pf :=
  let T := type of pf in
  lazymatch goal with
  | [ H : T |- _ ] => fail
  | _ => pose proof pf
  end.

Ltac saturate_mod_div :=
  repeat match goal with
         | [ |- context[?x mod ?y] ] => unique_pose_proof (Z_zerop_or (x / y))
         | [ H : context[?x mod ?y] |- _ ] => unique_pose_proof (Z_zerop_or (x / y))
         | [ |- context[?x / ?y] ] => unique_pose_proof (Z_zerop_or y)
         | [ H : context[?x / ?y] |- _ ] => unique_pose_proof (Z_zerop_or y)
         end.

Ltac t := intros; saturate_mod_div; try nia.

Ltac destr_step :=
  match goal with
  | [ H : and _ _ |- _ ] => destruct H
  | [ H : or _ _ |- _ ] => destruct H
  end.

Example mod_0_l: forall x : Z, 0 mod x = 0. Proof. t. Qed.
Example mod_0_r: forall x : Z, x mod 0 = 0. Proof. intros; nia. Qed.
Example Z_mod_same_full: forall a : Z, a mod a = 0. Proof. t. Qed.
Example Zmod_0_l: forall a : Z, 0 mod a = 0. Proof. t. Qed.
Example Zmod_0_r: forall a : Z, a mod 0 = 0. Proof. intros; nia. Qed.
Example mod_mod_same: forall x y : Z, (x mod y) mod y = x mod y. Proof. t. Qed.
Example Zmod_mod: forall a n : Z, (a mod n) mod n = a mod n. Proof. t. Qed.
Example Zmod_1_r: forall a : Z, a mod 1 = 0. Proof. intros; nia. Qed.
Example Zmod_div: forall a b : Z, a mod b / b = 0. Proof. intros; nia. Qed.
Example Z_mod_1_r: forall a : Z, a mod 1 = 0. Proof. intros; nia. Qed.
Example Z_mod_same: forall a : Z, a > 0 -> a mod a = 0. Proof. t. Qed.
Example Z_mod_mult: forall a b : Z, (a * b) mod b = 0.
Proof.
  intros a b.
  assert (b = 0 \/ (a * b) / b = a) by nia.
  nia.
Qed.
Example Z_mod_same': forall a : Z, a <> 0 -> a mod a = 0. Proof. t. Qed.
Example Z_mod_0_l: forall a : Z, a <> 0 -> 0 mod a = 0. Proof. t. Qed.
Example Zmod_opp_opp: forall a b : Z, - a mod - b = - (a mod b).
Proof.
  intros a b.
  pose proof (Z_eq_dec_or ((-a)/(-b)) (a/b)).
  nia.
Qed.
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
Example Zmult_mod_distr_r: forall a b c : Z, (a * c) mod (b * c) = a mod b * c.
Proof.
  intros a b c.
  destruct (Z_zerop c); try nia.
  pose proof (Z_eq_dec_or ((a * c) / (b * c)) (a / b)).
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
Example Zmult_mod_distr_l: forall a b c : Z, (c * a) mod (c * b) = c * (a mod b).
Proof.
  intros a b c.
  destruct (Z_zerop c); try nia.
  pose proof (Z_eq_dec_or ((c * a) / (c * b)) (a / b)).
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
Example Z_mod_mul: forall a b : Z, b <> 0 -> (a * b) mod b = 0.
Proof.
  intros a b.
  pose proof (Z_eq_dec_or ((a*b)/b) a).
  nia.
Qed.
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
Example Z_mod_opp_opp: forall a b : Z, b <> 0 -> - a mod - b = - (a mod b).
Proof.
  intros a b.
  pose proof (Z_eq_dec_or ((-a)/(-b)) ((a/b))).
  nia.
Qed.
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
  assert (a mod b <> 0 -> a / -b = -(a/b)-1) by t.
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
  assert (a mod b <> 0 -> -a/b = -1-a/b) by nia.
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
  assert (a mod b <> 0 -> a/(-b) = -1-a/b) by nia.
  nia.
Qed.
Example Z_mul_mod_distr_r: forall a b c : Z, b <> 0 -> c <> 0 -> (a * c) mod (b * c) = a mod b * c.
Proof.
  intros a b c.
  pose proof (Z_eq_dec_or ((a*c)/(b*c)) (a/b)).
  nia.
Qed.
Example Z_mul_mod_distr_l: forall a b c : Z, b <> 0 -> c <> 0 -> (c * a) mod (c * b) = c * (a mod b).
Proof.
  intros a b c.
  pose proof (Z_eq_dec_or ((c*a)/(c*b)) (a/b)).
  nia.
Qed.
Example Z_mod_opp_l_nz: forall a b : Z, b <> 0 -> a mod b <> 0 -> - a mod b = b - a mod b.
Proof.
  intros a b.
  assert (a mod b <> 0 -> -a/b = -1-a/b) by nia.
  nia.
Qed.
Example mod_eq: forall x x' y : Z, x / y = x' / y -> x mod y = x' mod y -> y <> 0 -> x = x'. Proof. intros; nia. Qed.
Example Z_div_nz_opp_r: forall a b : Z, a mod b <> 0 -> a / - b = - (a / b) - 1. Proof. intros; nia. Qed.
Example Z_div_nz_opp_full: forall a b : Z, a mod b <> 0 -> - a / b = - (a / b) - 1. Proof. intros; nia. Qed.
Example Zmod_unique: forall a b q r : Z, 0 <= r < b -> a = b * q + r -> r = a mod b.
Proof.
  intros a b q r ??.
  assert (q = a / b) by nia.
  nia.
Qed.
Example Z_mod_unique_neg: forall a b q r : Z, b < r <= 0 -> a = b * q + r -> r = a mod b.
Proof.
  intros a b q r ??.
  assert (q = a / b) by nia.
  nia.
Qed.
Example Z_mod_unique_pos: forall a b q r : Z, 0 <= r < b -> a = b * q + r -> r = a mod b.
Proof.
  intros a b q r ??.
  assert (q = a / b) by nia.
  nia.
Qed.
Example Z_rem_mul_r: forall a b c : Z, b <> 0 -> 0 < c -> a mod (b * c) = a mod b + b * ((a / b) mod c).
Proof.
  intros a b c ??.
  assert (a / (b * c) = ((a / b) / c)) by nia.
  nia.
Qed.
Example Z_mod_bound_or: forall a b : Z, b <> 0 -> 0 <= a mod b < b \/ b < a mod b <= 0. Proof. intros; nia. Qed.
Example Z_div_opp_l_nz: forall a b : Z, b <> 0 -> a mod b <> 0 -> - a / b = - (a / b) - 1. Proof. intros; nia. Qed.
Example Z_div_opp_r_nz: forall a b : Z, b <> 0 -> a mod b <> 0 -> a / - b = - (a / b) - 1. Proof. intros; nia. Qed.
Example Z_mod_small_iff: forall a b : Z, b <> 0 -> a mod b = a <-> 0 <= a < b \/ b < a <= 0. Proof. t. Qed.
Example Z_mod_unique: forall a b q r : Z, 0 <= r < b \/ b < r <= 0 -> a = b * q + r -> r = a mod b.
Proof.
  intros a b q r ??.
  assert (q = a/b) by nia.
  nia.
Qed.
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
Example Zdiv_mult_cancel_r: forall a b c : Z, c <> 0 -> a * c / (b * c) = a / b. Proof. intros; nia. Qed.
Example Z_div_unique_exact: forall a b q : Z, b <> 0 -> a = b * q -> q = a / b. Proof. intros; nia. Qed.
Example Zdiv_mult_cancel_l: forall a b c : Z, c <> 0 -> c * a / (c * b) = a / b. Proof. intros; nia. Qed.
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
Example Zdiv_Zdiv: forall a b c : Z, 0 <= b -> 0 <= c -> a / b / c = a / (b * c). Proof. intros; nia. Qed.
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
