Require Import Coq.Logic.HLevels. (* TODO: refactor to not Require funext *)
Require Import Coq.Bool.Bool.

(* TODO: move to Bool *)
Lemma Is_true_hprop b : IsHProp (Is_true b).
Proof. destruct b; auto using true_hprop, false_hprop. Qed.
Definition transparent_true (b : bool) : (True -> Is_true b) -> Is_true b :=
  match b with
  | true => fun _ => I
  | false => fun H => False_rect _ (H I)
  end.


Require Import Coq.NArith.NArith Coq.ZArith.ZArith Coq.Bool.Bool Coq.micromega.Lia.
Local Open Scope Z_scope.

Record Zmod (m : positive) := of_N_value {
  to_N : N ; _ : Is_true (to_N <? N.pos m)%N }.
Arguments to_N {m}.

(** Conversions to N *)

Lemma to_N_inj {m} (x y : Zmod m) : to_N x = to_N y -> x = y.
Proof. cbv [to_N]; destruct x, y, 1. apply f_equal, Is_true_hprop. Qed.

Lemma to_N_of_N_value {m} n pf : to_N (of_N_value m n pf) = n. Proof. trivial. Qed.

Lemma to_N_range {m} (x : Zmod m) : (to_N x < N.pos m)%N.
Proof. case x as [x H]; cbn [to_N]. apply N.ltb_lt, Is_true_eq_true, H. Qed.

Definition of_small_N m (n : N) (H : True -> (n < N.pos m)%N) : Zmod m.
  refine (of_N_value m n (transparent_true _ (fun _ => _))).
  abstract (apply Is_true_eq_left, N.ltb_lt, H, I).
Defined.

Lemma to_N_of_small_N {m} n pf : to_N (of_small_N m n pf) = n. Proof. trivial. Qed.

Definition of_N (m : positive) (n : N) : Zmod m.
  refine (of_small_N m (n mod (N.pos m)) (fun _ => _)).
  abstract (apply N.mod_upper_bound; discriminate).
Defined.

Lemma of_small_N_ok {m} n pf : of_small_N m n pf = of_N m n.
Proof. apply to_N_inj; apply eq_sym, N.mod_small, pf, I. Qed.

Lemma to_N_of_N {m} n : to_N (of_N m n) = (n mod (N.pos m))%N.
Proof. trivial. Qed.

Lemma of_N_to_N {m} x : of_N m (to_N x) = x.
Proof. apply to_N_inj. rewrite to_N_of_N, N.mod_small; trivial; apply to_N_range. Qed.

(** Conversions to nat *)

Definition of_nat m (a : nat) := of_N m (N.of_nat a).
Definition to_nat {m} (a : Zmod m) := N.to_nat (to_N a).

Lemma of_nat_to_nat {m} a : of_nat m (to_nat a) = a.
Proof. cbv [of_nat to_nat]. rewrite N2Nat.id, of_N_to_N; trivial. Qed.

Lemma to_nat_of_nat {m} a : to_nat (of_nat m a) = Nat.modulo a (Pos.to_nat m).
Proof. cbv [of_nat to_nat]. rewrite to_N_of_N, N2Nat.inj_mod, Nat2N.id, positive_N_nat; trivial. Qed.

Lemma to_nat_inj {m} a b : @to_nat m a = to_nat b -> a = b.
Proof. intros H. apply to_N_inj, N2Nat.inj, H. Qed.

(** Conversions to Z *)

Definition to_Z {m} (x : Zmod m) := Z.of_N (to_N x).
Notation unsigned := to_Z (only parsing).

Lemma to_Z_inj m (x y : Zmod m) : to_Z x = to_Z y -> x = y.
Proof. intros H. apply to_N_inj, N2Z.inj, H. Qed.

Lemma to_Z_range {m} (x : Zmod m) : 0 <= to_Z x < Z.pos m.
Proof.
  cbv [to_Z]; pose proof to_N_range x.
  apply N2Z.inj_lt in H; auto using N2Z.is_nonneg.
Qed.

Lemma mod_to_Z {m} (x : Zmod m) : to_Z x mod (Z.pos m) = to_Z x.
Proof. rewrite Z.mod_small; auto using to_Z_range. Qed.

Definition of_small_Z (m : positive) (z : Z) (H : True -> 0 <= z < Z.pos m) : Zmod m.
  refine (of_small_N m (Z.to_N z) (fun _ => _)).
  abstract (case (H I) as [Hl Hu]; apply Z2N.inj_lt in Hu; trivial using Pos2Z.is_nonneg).
Defined.

Definition of_Z (m : positive) (z : Z) : Zmod m.
  refine (of_small_Z m (z mod (Z.pos m)) (fun _ => _)).
  abstract (apply Z.mod_pos_bound, Pos2Z.is_pos).
Defined.

Lemma of_small_Z_ok {m} z H : of_small_Z m z H = of_Z m z.
Proof. apply to_N_inj; cbv [to_N]. apply f_equal, eq_sym, Z.mod_small, H, I. Qed.

Lemma to_Z_of_Z {m} z : to_Z (of_Z m z) = z mod (Z.pos m).
Proof. apply Z2N.id, Z.mod_pos_bound, eq_refl. Qed.

Lemma of_Z_to_Z {m} x : of_Z m (to_Z x) = x.
Proof. apply to_Z_inj. rewrite to_Z_of_Z, Z.mod_small; trivial; apply to_Z_range. Qed.

(* Converting N<->Z through Zmod *)

Lemma to_Z_of_N_value {m} n pf : to_Z (of_N_value m n pf) = Z.of_N n. Proof. trivial. Qed.

Lemma to_Z_of_N {m} n : to_Z (of_N m n) = (Z.of_N n) mod (Z.pos m).
Proof. cbv [to_Z]. rewrite to_N_of_N, N2Z.inj_mod; trivial. Qed.

Lemma to_N_of_Z {m} z : to_N (of_Z m z) = Z.to_N (z mod (Z.pos m)).
Proof. trivial. Qed.

Module Import Coercions.
  Coercion Z.pos : positive >-> Z.
  Coercion N.pos : positive >-> N.
  Coercion Z.of_N : N >-> Z.
  Coercion to_Z : Zmod >-> Z.
  Coercion to_N : Zmod >-> N.
End Coercions.
Local Set Printing Coercions.

(** Constants *)
Notation zero := (of_N_value _ 0 I).
Notation one := (of_N _ 1).
Lemma to_N_0 {m} : @to_N m zero = 0%N. Proof. trivial. Qed.
Lemma to_Z_0 {m} : @to_Z m zero = 0. Proof. trivial. Qed.
Lemma of_Z_0 {m} : of_Z m 0 = zero. Proof. trivial. Qed.
Lemma of_N_0 {m} : of_N m 0 = zero. Proof. trivial. Qed.
Lemma of_N_1 {m} : of_N m 1 = one. Proof. trivial. Qed.
Lemma of_Z_1 {m} : of_Z m 1 = one.
Proof. apply to_Z_inj. rewrite to_Z_of_Z, to_Z_of_N; trivial. Qed.

Definition elements m : list (Zmod m) := List.map (of_nat m) (List.seq 0 (Pos.to_nat m)).

(* TODO: move *)
Module List.
  Import List.
  Lemma hd_error_skipn {A} n : forall xs, @hd_error A (skipn n xs) = nth_error xs n.
  Proof. induction n, xs; cbn [hd_error skipn]; auto. Qed.

  Lemma skipn_seq n : forall start len, skipn n (seq start len) = seq (start+n) (len-n).
  Proof. induction n, len; cbn [skipn seq]; rewrite ?Nat.add_0_r, ?IHn; auto. Qed.

  Lemma nth_error_seq n start len : nth_error (seq start len) n = 
    if Nat.ltb n len then Some (Nat.add start n) else None.
  Proof.
    rewrite <-hd_error_skipn, skipn_seq.
    destruct (Nat.sub len n) eqn:?, (Nat.ltb_spec n len); cbn [nth_error seq]; trivial; lia.
  Qed.
End List.

Lemma nth_error_elements {m} n : List.nth_error (elements m) n =
  if (Nat.ltb n (Pos.to_nat m)) then Some (of_nat _ n) else None.
Proof.
  cbv [elements].
  rewrite List.nth_error_map, List.nth_error_seq.
  case Nat.ltb; trivial.
Qed.

Definition In_elements {m} a : List.In a (elements m).
Proof.
  apply List.nth_error_In with (n:=to_nat a); rewrite nth_error_elements.
  cbv [to_nat]; pose proof to_N_range a.
  destruct (Nat.ltb_spec (N.to_nat (to_N a)) (Pos.to_nat m)); [|lia].
  apply f_equal, of_nat_to_nat.
Qed.

Lemma NoDup_elements {m} : List.NoDup (elements m).
Proof.
  cbv [elements].
  eapply List.NoDup_map_inv with (f:=to_nat).
  erewrite List.map_map, List.map_ext_in, List.map_id; trivial using List.seq_NoDup.
  intros a Ha. apply List.in_seq in Ha; cbn [Nat.add] in Ha.
  rewrite to_nat_of_nat, Nat.mod_small; intuition idtac.
Qed.

(** Operations *)

Definition eqb {m} (x y : Zmod m) := N.eqb (to_N x) (to_N y).
Lemma eqb_spec {m} (x y : Zmod m) : BoolSpec (x = y) (x <> y) (eqb x y).
Proof.
  cbv [eqb]. case (N.eqb_spec (to_N x) (to_N y));
    constructor; auto using to_N_inj; congruence.
Qed.
(* TODO: eq_dec ? *)

Definition add {m} (x y : Zmod m) : Zmod m.
  refine (let n := x + y in of_small_N m (if N.ltb n m then n else n-m) (fun _ => _))%N.
  abstract (pose proof to_N_range x; pose proof to_N_range y; case (N.ltb_spec n m); lia).
Defined.

Lemma to_N_add {m} (x y : Zmod m) : to_N (add x y) = ((to_N x + to_N y) mod m)%N.
Proof.
  pose proof to_N_range x; pose proof to_N_range y.
  cbv [add]. rewrite of_small_N_ok, to_N_of_N.
  case (N.ltb_spec (x + y) m) as [?|?].
  { rewrite N.mod_small; trivial. }
  { apply N2Z.inj; rewrite 2N2Z.inj_mod.
    symmetry; rewrite <-Z_mod_plus_full with (b:=-1).
    rewrite N2Z.inj_sub; trivial. }
Defined.

Lemma to_Z_add {m} (x y : Zmod m) : to_Z (add x y) = (to_Z x + to_Z y) mod m.
Proof. cbv [to_Z]. rewrite to_N_add, N2Z.inj_mod; f_equal; zify; trivial. Qed.

Definition sub {m} (x y : Zmod m) : Zmod m.
  refine (let z := x - y in of_small_Z m (if Z.leb 0 z then z else z+m) (fun _ => _)).
  abstract (pose proof to_Z_range x; pose proof to_Z_range y; case (Z.leb_spec 0 z); lia).
Defined.

Lemma to_Z_sub {m} (x y : Zmod m) : to_Z (sub x y) = (to_Z x - to_Z y) mod m.
Proof.
  pose proof to_Z_range x; pose proof to_Z_range y.
  cbv [sub]. rewrite of_small_Z_ok, to_Z_of_Z.
  case (Z.leb_spec 0 (x - y)) as [?|?].
  { rewrite Z.mod_small; lia. }
  { symmetry; rewrite <-Z_mod_plus_full with (b:=1); trivial. }
Qed.

Lemma to_N_sub {m} (x y : Zmod m) : to_N (sub x y) = Z.to_N ((to_N x - to_N y) mod m).
Proof.
  pose proof to_Z_sub x y.
  pose proof to_Z_range (sub x y).
  cbv [to_Z] in *; lia.
Qed.

Definition opp {m} (x : Zmod m) : Zmod m := sub zero x.

Lemma to_Z_opp {m} (x : Zmod m) : to_Z (opp x) = (- to_Z x) mod m.
Proof. apply to_Z_sub. Qed.

Lemma to_N_opp {m} (x : Zmod m) : to_N (opp x) = Z.to_N ((- to_N x) mod m).
Proof. apply to_N_sub. Qed.

Definition mul {m} (x y : Zmod m) : Zmod m := of_N m (to_N x * to_N y).

Lemma to_N_mul {m} (x y : Zmod m) : to_N (mul x y) = ((to_N x * to_N y) mod m)%N.
Proof. cbv [mul]; rewrite ?to_N_of_Z; trivial. Qed.

Lemma to_Z_mul {m} (x y : Zmod m) : to_Z (mul x y) = (to_Z x * to_Z y) mod m.
Proof. cbv [to_Z]. rewrite to_N_mul, N2Z.inj_mod; lia. Qed.

Local Ltac r := try apply to_Z_inj;
  (* Note: rewrite is slow, and autorewrite isn't faster *)
  repeat rewrite ?to_Z_of_Z, ?to_Z_add, ?to_Z_mul, ?to_Z_sub, ?to_Z_opp,
    ?mod_to_Z, ?Z.mod_0_l, ?Z.mul_1_l, ?Z.add_0_l, ?Z.add_mod_idemp_l,
    ?Z.add_mod_idemp_r, ?Z.mul_mod_idemp_l, ?Z.mul_mod_idemp_r,
    ?Z.add_opp_diag_r, ?to_Z_of_N_value, ?to_Z_of_N;
  try (f_equal; lia).

Lemma add_0_l {m} a : @add m zero a = a. Proof. r. Qed.
Lemma add_comm {m} a b : @add m a b = add b a. Proof. r. Qed.
Lemma mul_comm {m} a b : @mul m a b = mul b a. Proof. r. Qed.
Lemma add_assoc {m} a b c : @add m a (add b c) = add (add a b) c. Proof. r. Qed.
Lemma mul_assoc {m} a b c : @mul m a (mul b c) = mul (mul a b) c. Proof. r. Qed.
Lemma mul_add_l {m} a b c : @mul m (add a b) c = add (mul a c) (mul b c). Proof. r. Qed.
Lemma mul_1_l {m} a : @mul m one a = a. Proof. r. Qed.
Lemma add_opp_r {m} a b : @add m a (opp b) = sub a b. Proof. r. Qed.
Lemma add_opp_same_r {m} a : @add m a (opp a) = zero. Proof. r. Qed.

Lemma sub_same {m} a : @sub m a a = zero.
Proof. rewrite <-add_opp_r, add_opp_same_r; trivial. Qed.

Lemma ring_theory m : @ring_theory (Zmod m) zero one add mul sub opp eq.
Proof. split; auto using eq_sym, add_0_l, add_comm, mul_comm, add_assoc, mul_assoc, mul_add_l, mul_1_l, add_opp_r, add_opp_same_r. Qed.

Lemma mul_1_r {m} a : @mul m a one = a. Proof. rewrite <-mul_comm; apply mul_1_l. Qed.
Lemma mul_0_l {m} a : @mul m zero a = zero. Proof. r. Qed.
Lemma mul_0_r {m} a : @mul m a zero = zero. Proof. rewrite <-mul_comm; apply mul_0_l. Qed.

(* TODO: move *)
Module Pos.
  Lemma iter_op_correct {A} op x p zero
    (op_zero_r : op x zero = x)
    (op_assoc : forall x y zero : A, op x (op y zero) = op (op x y) zero)
    : @Pos.iter_op A op p x = Pos.iter (op x) zero p.
  Proof.
    induction p using Pos.peano_ind; cbn;
      rewrite ?Pos.iter_op_succ, ?Pos.iter_succ, ?IHp; auto.
  Qed.
End Pos.
Module N.
  Definition iter_op {A} (op : A -> A -> A) (zero x : A) (n : N) :=
    match n with N0 => zero | Npos p => Pos.iter_op op p x end.

  Lemma iter_op_0_r {A} op zero x : @iter_op A op zero x 0 = zero. Proof. trivial. Qed.

  Lemma iter_op_1_r {A} op zero x : @iter_op A op zero x 1 = x. Proof. trivial. Qed.

  Lemma iter_op_succ_r {A} op zero x n
    (opp_zero_r : x = op x zero)
    (op_assoc  : forall x y z : A, op x (op y z) = op (op x y) z)
    : @iter_op A op zero x (N.succ n) = op x (iter_op op zero x n).
  Proof. case n; cbn; auto using Pos.iter_op_succ. Qed.

  Lemma iter_op_add_r {A} op zero x n
    (opp_zero_r : x = op x zero)
    (op_assoc  : forall x y z : A, op x (op y z) = op (op x y) z)
    : @iter_op A op zero x (N.succ n) = op x (iter_op op zero x n).
  Proof. induction n using N.peano_ind; cbn; rewrite ?iter_op_succ_r; auto. Qed.

  Lemma iter_op_correct {A} op zero x n
    (opp_zero_r : x = op x zero)
    (op_assoc  : forall x y z : A, op x (op y z) = op (op x y) z)
    : @iter_op A op zero x n = N.iter n (op x) zero.
  Proof. case n; cbn; auto using Pos.iter_op_correct. Qed.
End N.

Definition pow_N {m} (a : Zmod m) n := N.iter_op mul one a n.

Lemma pow_N_correct {m} a n
  : @pow_N m a n = N.iter n (mul a) one.
Proof. apply N.iter_op_correct; auto using mul_1_r, mul_assoc. Qed.

Lemma pow_N_0_r {m} (x : Zmod m) : @pow_N m x 0 = one.
Proof. rewrite pow_N_correct; reflexivity. Qed.

Lemma pow_N_succ_r {m} (x : Zmod m) n : pow_N x (N.succ n) = mul x (pow_N x n).
Proof. rewrite !pow_N_correct, N.iter_succ; trivial. Qed.

Lemma to_N_pow_N {m} x n : @to_N m (pow_N x n) = (to_N x ^ n mod m)%N.
Proof.
  revert x; induction n using N.peano_ind; intros; rewrite
    ?pow_N_succ_r, ?to_N_mul, ?N.pow_succ_r', ?IHn, ?N.Div0.mul_mod_idemp_r; trivial.
Qed.

Lemma pow_N_0_l {m} n (Hn : n <> 0%N) : @pow_N m zero n = zero.
Proof. apply to_N_inj; rewrite ?to_N_pow_N, to_N_0, ?N.pow_0_l; trivial. Qed.

Lemma pow_N_1_l {m} n : @pow_N m one n = one.
Proof.
  induction n using N.peano_ind; auto using mul_1_l.
  rewrite ?pow_N_succ_r, IHn, mul_1_l; trivial.
Qed.

Lemma pow_N_add_r {m} (x : Zmod m) a b : pow_N x (a+b) = mul (pow_N x a) (pow_N x b).
Proof.
  apply to_N_inj; rewrite ?to_N_pow_N, ?N.pow_add_r, ?to_N_mul, ?to_N_pow_N;
  auto using N.Div0.mul_mod.
Qed.

(* TODO: move *)
Module Import NN.
Module N.
  Lemma mod_pow_l a b c : ((a mod c)^b mod c = ((a ^ b) mod c))%N.
  Proof.
    induction b using N.peano_ind; intros; trivial; pose proof N.Div0.mul_mod.
    rewrite ?N.pow_succ_r', <-N.Div0.mul_mod_idemp_r, IHb; auto.
  Qed.
End N.
End NN.

Lemma pow_N_mul_r {m} (x : Zmod m) a b : pow_N x (a*b) = pow_N (pow_N x a) b.
Proof. apply to_N_inj; rewrite ?to_N_pow_N, ?N.pow_mul_r, ?N.mod_pow_l; trivial. Qed.

Lemma pow_N_mul_l {m} (x y : Zmod m) n : pow_N (mul x y) n = mul (pow_N x n) (pow_N y n).
Proof.
  apply to_N_inj; pose proof N.Div0.mul_mod.
  rewrite ?to_N_pow_N, ?to_N_mul, ?N.mod_pow_l, ?N.pow_mul_l, ?to_N_pow_N; auto.
Qed.

(** Additional operations for prime m *)
(* TODO: move to Znmutheory? *)
Require Import Znumtheory.
Module Import Znumtheory.

Definition invmod a m := fst (fst (extgcd a m)).

Lemma invmod_0_l m : invmod 0 m = 0. Proof. reflexivity. Qed.

Lemma invmod_ok a m (Hm : m <> 0) : invmod a m * a mod m = Z.gcd a m mod m.
Proof.
  cbv [invmod]; destruct extgcd as [[u v]g] eqn:H.
  eapply extgcd_correct in H; case H as [[]]; subst; cbn [fst snd].
  erewrite <-Z.mod_add, H; trivial.
Qed.

Lemma invmod_coprime' a m (Hm : m <> 0) (H : Z.gcd a m = 1) : invmod a m * a mod m = 1 mod m.
Proof. rewrite invmod_ok, H; trivial. Qed.

Lemma invmod_coprime a m (Hm : 2 <= m) (H : Z.gcd a m = 1) : invmod a m * a mod m = 1.
Proof. rewrite invmod_coprime', Z.mod_1_l; lia. Qed.

Lemma invmod_prime a m (Hm : prime m) (H : a mod m <> 0) : invmod a m * a mod m = 1.
Proof.
  pose proof prime_ge_2 _ Hm as Hm'. rewrite Z.mod_divide in H by lia.
  apply invmod_coprime, Zgcd_1_rel_prime, rel_prime_sym, prime_rel_prime; auto.
Qed.

Lemma cong_iff_0 a b m : a mod m = b mod m <-> (a - b) mod m = 0.
Proof.
  case (Z.eq_dec m 0) as [->|Hm]; [rewrite ?Zmod_0_r; lia|].
  split; intros H. { rewrite Zminus_mod, H, Z.sub_diag, Z.mod_0_l; trivial. }
  apply Zmod_divides in H; trivial; case H as [c H].
  replace b with (a + (-c) * m) by lia; rewrite Z.mod_add; trivial.
Qed.

Lemma cong_iff_ex a b m (Hm : m <> 0) : a mod m = b mod m <-> exists n, a - b = n * m.
Proof. rewrite cong_iff_0, Z.mod_divide by trivial; reflexivity. Qed.

Lemma cong_mul_cancel_r_coprime a b m (Hm : m <> 0) (Hb : Z.gcd b m = 1)
  (H : (a * b) mod m = 0) : a mod m = 0.
Proof.
  apply Zmod_divide in H; trivial; [].
  rewrite Z.mul_comm in H; apply Gauss, Zdivide_mod in H; trivial.
  apply rel_prime_sym, Zgcd_1_rel_prime; trivial.
Qed.

Theorem chinese_remainder a m1 b m2
  (Hm1 : m1 <> 0) (Hm2 : m2 <> 0) (H : Z.gcd m1 m2 = 1)
  (H1 : a mod m1 = b mod m1) (H2 : a mod m2 = b mod m2) :
  a mod (m1 * m2) = b mod (m1 * m2).
Proof.
  apply cong_iff_0; apply cong_iff_0 in H2.
  apply cong_iff_ex in H1; trivial; []; case H1 as [k H1]. rewrite H1 in *.
  apply cong_mul_cancel_r_coprime in H2; trivial.
  rewrite Z.mul_comm, Zmult_mod_distr_l. rewrite H2, Z.mul_0_r; trivial.
Qed.



Definition solvecong (m1 m2 : Z) :=
  let '(a, b, d) := extgcd m1 m2 in
  fun (r1 r2 : Z) => r1 - (r1 - r2)/d*a*m1.

Lemma solvecong_correct m1 m2 r1 r2 (H : (r1 - r2) mod (Z.gcd m1 m2) = 0)
  (x := solvecong m1 m2 r1 r2) : x mod m1 = r1 mod m1 /\ x mod m2 = r2 mod m2.
Proof.
  cbv [solvecong] in *; case (extgcd m1 m2) as [[a b] d] eqn:E.
  eapply extgcd_correct in E; case E as [E D]; rewrite <-D in *; clear D.
  replace x with (r2 + (r1 - r2)/d*b*m2) at 2 by (Z.div_mod_to_equations; lia); cbv [x].
  rewrite <-Zminus_mod_idemp_r, <-Zplus_mod_idemp_r, 2Z_mod_mult, Z.add_0_r, Z.sub_0_r; auto.
Qed.

Lemma solvecong_coprime m1 m2 r1 r2 (H : Z.gcd m1 m2 = 1)
  (x := solvecong m1 m2 r1 r2) : x mod m1 = r1 mod m1 /\ x mod m2 = r2 mod m2.
Proof. apply solvecong_correct. rewrite H, Z.mod_1_r; trivial. Qed.

Lemma chinese_remainder_solvecong a r1 m1 r2 m2
  (H : Z.gcd m1 m2 = 1) (Hm1 : m1 <> 0) (Hm2 : m2 <> 0)
  (H1 : a mod m1 = r1 mod m1) (H2 : a mod m2 = r2 mod m2) :
  a mod (m1 * m2) = solvecong m1 m2 r1 r2 mod (m1 * m2).
Proof.
  case (solvecong_coprime m1 m2 r1 r2 H) as [].
  eapply chinese_remainder; congruence.
Qed.

Lemma solvecong_comm m1 m2 r1 r2
  (H : Z.gcd m1 m2 = 1) (Hm1 : m1 <> 0) (Hm2 : m2 <> 0) :
  solvecong m1 m2 r1 r2 mod (m1 * m2) = solvecong m2 m1 r2 r1 mod (m1 * m2).
Proof.
  rewrite Z.mul_comm at 2.
  case (solvecong_coprime m1 m2 r1 r2 H) as [].
  erewrite <-(chinese_remainder_solvecong _ r1); try assumption.
  symmetry; erewrite <-(chinese_remainder_solvecong _ r2); try assumption.
  { rewrite Z.mul_comm; trivial. }
  { rewrite Z.gcd_comm; trivial. }
  instantiate (1:=solvecong m1 m2 r1 r2).
  all : assumption.
Qed.

End Znumtheory.

Lemma chinese_remainder_solvecong_Zmod
  (a b : positive) (H : Z.gcd a b = 1) (x : Zmod a) (y : Zmod b)
  z (Hx : z mod a = x) (Hy : z mod b = y) :
  of_Z _ z = of_Z _ (solvecong a b x y) :> Zmod (a*b).
Proof.
  apply to_Z_inj; rewrite !to_Z_of_Z, !Pos2Z.inj_mul.
  apply chinese_remainder_solvecong;
    rewrite ?Hx, ?Hy, ?mod_to_Z; trivial; inversion 1.
Qed.

Definition inv {m} (x : Zmod m) : Zmod m := of_Z m (invmod (to_Z x) m).
Definition ndiv {m} (x y : Zmod m) : Zmod m := of_Z m (invmod (to_Z y) m * x).

Module Import Notations.
  Declare Scope Zmod_scope.
  Delimit Scope Zmod_scope with Zmod.
  (* Bind Scope Zmod_scope with Zmod. *)
  Infix "*" := mul : Zmod_scope.
  Infix "+" := add : Zmod_scope.
  Infix "-" := sub : Zmod_scope.
  Infix "/" := ndiv : Zmod_scope.
  Infix "=?" := eqb : Zmod_scope.
  Notation "- x" := (opp x) : Zmod_scope.
End Notations.

Lemma to_Z_inv {m} x : to_Z (@inv m x) = invmod x m mod m.
Proof. cbv [inv]. rewrite to_Z_of_Z. trivial. Qed.

Lemma to_N_1 {m : positive} (Hm : 2 <= m) : @to_N m one = 1%N.
Proof. rewrite to_N_of_N, N.mod_small; lia. Qed.

Lemma to_Z_1 {m : positive} (Hm : 2 <= m) : @to_Z m one = 1.
Proof. rewrite to_Z_of_N, Z.mod_small; lia. Qed.

Lemma hprop_Zmod_1 (a b : Zmod 1) : a = b.
Proof.
  pose proof to_N_range a; pose proof to_N_range b; apply to_N_inj; lia.
Qed.

Lemma wlog_eq_Zmod_2 {m} (a b : Zmod m) (k : 2 <= m -> a = b) : a = b.
Proof.
  destruct (Pos.eq_dec 1 m) as [e|ne].
  { destruct e; auto using hprop_Zmod_1. }
  { apply k; lia. }
Qed.

Lemma one_neq_zero {m : positive} (Hm : 2 <= m) : one <> zero :> Zmod m.
Proof.
  intro H. apply (f_equal to_N) in H.
  rewrite to_N_1, to_N_0 in H; lia.
Qed.

Lemma to_N_nz {m} (x : Zmod m) (H : x <> zero) : to_N x <> 0%N.
Proof. intros X; apply H, to_N_inj. rewrite X; trivial. Qed.

Lemma to_Z_nz {m} (x : Zmod m) (H : x <> zero) : to_Z x <> 0.
Proof. intros X; apply H, to_Z_inj. rewrite X; trivial. Qed.

Lemma mul_inv_l {m} (x y : Zmod m) : mul (inv y) x = ndiv x y.
Proof.
  apply to_Z_inj. cbv [ndiv inv].
  rewrite to_Z_mul, !to_Z_of_Z, !Z.mul_mod_idemp_l; auto; inversion 1.
Qed.

Lemma mul_inv_r {m} (x y : Zmod m) : mul x (inv y) = ndiv x y.
Proof. rewrite mul_comm, mul_inv_l; trivial. Qed.

Lemma div_same {m} (a : Zmod m) : ndiv a a = of_Z m (Z.gcd a m).
Proof.
  rewrite <-mul_inv_l. apply to_Z_inj. rewrite to_Z_mul, to_Z_inv,
    Z.mul_mod_idemp_l, to_Z_of_Z, invmod_ok by inversion 1; trivial.
Qed.

Lemma div_same_coprime {m} (a : Zmod m) (H : Z.gcd a m = 1) : ndiv a a = one.
Proof. rewrite div_same, H, of_Z_1; trivial. Qed.

Lemma div_same_prime {m} (x : Zmod m) (Hm : prime m) (H : x <> zero) : ndiv x x = one.
Proof.
  apply to_Z_inj. apply to_Z_nz in H. pose proof to_Z_range x.
  rewrite <-mul_inv_l, to_Z_mul, to_Z_inv, Z.mul_mod_idemp_l, to_Z_1,
    invmod_prime; trivial; rewrite ?Z.mod_small; try lia.
Qed.

Lemma mul_inv_same_l_coprime {m} (x : Zmod m) (H : Z.gcd x m = 1) :
  mul (inv x) x = one.
Proof. apply wlog_eq_Zmod_2; rewrite ?mul_inv_r, ?mul_inv_l, ?div_same_coprime; trivial. Qed.

Lemma mul_inv_same_l_prime {m} (x : Zmod m) (Hm : prime m) (H : x <> zero) :
  mul (inv x) x = one.
Proof. intros; rewrite ?mul_inv_r, ?mul_inv_l, ?div_same_prime; trivial. Qed.

Lemma field_theory (m : positive) (Hm : prime m) :
  @Field_theory.field_theory (Zmod m) zero one add mul sub opp ndiv inv eq.
Proof.
  split; auto using ring_theory, one_neq_zero, prime_ge_2, mul_inv_r, mul_inv_same_l_prime.
Qed.

Lemma inv_nz_prime {m} (x : Zmod m) (Hm : prime m) (Hx : x <> zero) : inv x <> zero.
Proof.
  intro HX; exfalso; apply (@one_neq_zero m); auto using prime_ge_2.
  pose proof mul_inv_same_l_prime x Hm Hx as H; rewrite HX, mul_0_l in H; auto.
Qed.

Lemma inv_inv {m} (x : Zmod m) (Hm : prime m): inv (inv x) = x.
Proof.
  case (eqb_spec x zero) as [|Hx]; subst; pose proof @inv_nz_prime m.
  { apply to_Z_inj. rewrite to_Z_inv, invmod_0_l; trivial. }
  rewrite <-mul_1_r, <-(mul_inv_same_l_prime (inv x) Hm), (mul_comm _ (inv x)); auto.
  rewrite mul_assoc, (mul_comm x), (mul_inv_same_l_prime x Hm Hx), mul_1_l; auto.
Qed.

Lemma inv_0 {m} : @inv m zero = zero. Proof. trivial. Qed.

Lemma inv_1 {m} : @inv m one = one.
Proof.
  case (Pos.eq_dec m 1); intros; subst; trivial.
  symmetry; rewrite <-mul_1_l, mul_inv_r, div_same_coprime; trivial.
  rewrite to_Z_1, Z.gcd_1_l; lia.
Qed.

Lemma mul_cancel_l_coprime {m} (a b c : Zmod m)
  (Ha : Z.gcd a m = 1) (H : mul a b = mul a c) : b = c.
Proof.
  apply wlog_eq_Zmod_2; intros. apply (f_equal (fun x => mul (inv a) x)) in H.
  rewrite !mul_assoc, !mul_inv_same_l_coprime, !mul_1_l in H; trivial.
Qed.

Lemma mul_cancel_r_coprime {m} (a b c : Zmod m)
  (Ha : Z.gcd a m = 1) (H : mul b a = mul c a) : b = c.
Proof. rewrite 2(mul_comm _ a) in H; apply mul_cancel_l_coprime in H; trivial. Qed.

Lemma mul_cancel_l_prime {m} (a b c : Zmod m) (Hm : prime m) (Ha : a <> zero)
  (H : mul a b = mul a c) : b = c.
Proof.
  apply (f_equal (fun x => mul (inv a) x)) in H.
  rewrite !mul_assoc, !mul_inv_same_l_prime, !mul_1_l in H; trivial.
Qed.

Lemma mul_cancel_r_prime {m} (a b c : Zmod m) (Hm : prime m) (Ha : a <> zero)
  (H : mul b a = mul c a) : b = c.
Proof. rewrite 2(mul_comm _ a) in H; apply mul_cancel_l_prime in H; trivial. Qed.

Definition invertibles m : list (Zmod m) :=
  List.filter (fun x : Zmod m => Z.eqb (Z.gcd x m) 1) (elements m).

Lemma In_invertibles m (x : Zmod m) : List.In x (invertibles m) <-> Z.gcd x m = 1.
Proof.
  cbv [invertibles]. rewrite List.filter_In, Z.eqb_eq.
  intuition eauto using In_elements.
Qed.

Lemma NoDup_invertibles {m} : List.NoDup (invertibles m).
Proof. cbv [invertibles]. apply List.NoDup_filter, NoDup_elements. Qed.


Require Permutation.
Local Notation Permutation := Permutation.Permutation.

Lemma Permutation_mul_invertibles {m} (a : Zmod m) (H : Z.gcd a m = 1) :
  Permutation (List.map (mul a) (invertibles m)) (invertibles m).
Proof.
  eapply Permutation.NoDup_Permutation;
    try eapply FinFun.Injective_map_NoDup; cbv [FinFun.Injective];
    eauto using NoDup_invertibles, mul_cancel_l_coprime; intros.
  (*  List.In x (List.map (mul a) (invertibles m)) <-> List.In x (invertibles m) *)
  (* TODO: refactor, this should be the easy part *)
  rewrite In_invertibles, List.in_map_iff; setoid_rewrite In_invertibles; split.
  { intros (y&[]&Hy).
    rewrite to_Z_mul by discriminate.
    eapply Zgcd_1_rel_prime, rel_prime_mod, rel_prime_sym, rel_prime_mult; try lia.
    all : apply rel_prime_sym, Zgcd_1_rel_prime; trivial. }
  { exists (mul (inv a) x).
    rewrite mul_assoc, (mul_comm a), mul_inv_same_l_coprime, mul_1_l; try split; trivial.
    rewrite to_Z_mul, to_Z_inv.
    eapply Zgcd_1_rel_prime, rel_prime_mod, rel_prime_sym, rel_prime_mult; try lia.
    2 : solve [apply rel_prime_sym, Zgcd_1_rel_prime; trivial].
    eapply rel_prime_sym, rel_prime_mod; try lia.

    cbv [invmod].
    case extgcd as [[u v] g] eqn:e; apply extgcd_correct in e; case e as [e1 e2].
    rewrite H in e2; subst g.
    cbn [fst].
    eapply bezout_rel_prime.
    eapply Bezout_intro with (u:=to_Z a) (v:=v); lia. }
Qed.

Lemma prod_Permutation {m} (xs ys : list (Zmod m)) (H : Permutation xs ys) :
  List.fold_right mul one xs = List.fold_right mul one ys.
Proof. induction H; cbn; repeat rewrite ?mul_assoc, ?(mul_comm x); congruence. Qed.

Lemma prod_map_mul {m} (a : Zmod m) xs :
  List.fold_right mul one (List.map (mul a) xs) =
  mul (pow_N a (N.of_nat (length xs))) (List.fold_right mul one xs).
Proof.
  induction xs as [|x xs]; cbn [List.fold_right List.map length];
    rewrite ?pow_N_0_r, ?mul_1_r, ?Nat2N.inj_succ, ?pow_N_succ_r, ?IHxs; trivial.
  repeat rewrite ?mul_assoc, ?(mul_comm _ x); trivial.
Qed.

Theorem euler {m} (a : Zmod m) (H : Z.gcd a m = 1) :
  pow_N a (N.of_nat (length (invertibles m))) = one.
Proof.
  eapply wlog_eq_Zmod_2; intros Hm.
  epose proof prod_map_mul a (invertibles m) as P.
  erewrite prod_Permutation in P by (eapply Permutation_mul_invertibles, H).
  rewrite <-mul_1_l in P at 1; eapply mul_cancel_r_coprime, eq_sym in P; trivial.
  (* TODO: Z.gcd (to_Z (List.fold_right mul one (invertibles m))) (Z.pos m) = 1 *)
  (* Again, this should be the easy part... *)
  clear -Hm.
  pose proof proj2 (List.Forall_forall _ _) (fun x => proj1 (In_invertibles m x)).
  induction H; cbn [List.fold_right]; rewrite ?to_Z_1, ?Z.gcd_1_l, ?to_Z_mul; trivial.
  rewrite Z.gcd_mod, Z.gcd_comm by lia.
  eapply Zgcd_1_rel_prime, rel_prime_sym, rel_prime_mult;
  solve [apply rel_prime_sym, Zgcd_1_rel_prime; trivial].
Qed.


Definition pow_Z {m} (a : Zmod m) z :=
  if Z.ltb z 0 then inv (pow_N a (Z.abs_N z)) else pow_N a (Z.abs_N z).

Lemma pow_Z_0_r {m} (x : Zmod m) : @pow_Z m x 0 = one.
Proof. reflexivity. Qed.

Lemma pow_Z_0_l {m} z (Hn : z <> 0) : @pow_Z m zero z = zero.
Proof.
  cbv [pow_Z]; case (Z.ltb_spec z 0) as [];
    rewrite ?pow_N_0_l, ?inv_0; trivial; lia.
Qed.

Lemma pow_Z_1_l {m} z : @pow_Z m one z = one.
Proof.
  cbv [pow_Z]; case (Z.ltb_spec z 0) as [];
    rewrite ?pow_N_1_l, ?inv_1; trivial.
Qed.
Lemma pow_Z_N_r {m} (a : Zmod m) (n : N) : pow_Z a n = pow_N a n.
Proof. case n; trivial. Qed.

Lemma to_Z_pow_Z_pos {m} x z (Hz : 0 <= z) : @to_Z m (pow_Z x z) = x^z mod m.
Proof.
  cbv [pow_Z to_Z]; case (Z.ltb_spec z 0) as []; try lia.
  rewrite to_N_pow_N, N2Z.inj_mod, N2Z.inj_pow; f_equal; f_equal; lia.
Qed.

Lemma pow_Z_opp_r {m} (a : Zmod m) (z : Z) (Hm : prime m): pow_Z a (-z) = inv (pow_Z a z).
Proof.
  cbv [pow_Z]; case (Z.ltb_spec (-z) 0), (Z.ltb_spec z 0);
    try (replace z with 0%Z by lia); cbn;
    rewrite ?inv_inv, ?inv_1, ?Zabs2N.inj_opp; trivial.
Qed.

Lemma to_Z_pow_Z_neg {m} (x : Zmod m) z (Hm : prime m) (Hz : z <= 0) :
  @to_Z m (pow_Z x z) = invmod (to_Z x^(-z)) m mod m.
Proof.
  replace z with (--z) at 1 by lia; rewrite pow_Z_opp_r by trivial.
  rewrite to_Z_inv, to_Z_pow_Z_pos by lia. f_equal.
Abort.

Module Z.
  (** Modulo with an offset *)
  Definition omodulo d a b := Z.modulo (a - d) b + d.

  Lemma omodulo_0 a b : Z.omodulo 0 a b = Z.modulo a b.
  Proof. cbv [Z.omodulo]. rewrite Z.sub_0_r, Z.add_0_r; trivial. Qed.

  Lemma div_omod d a b : b <> 0 -> a = b * ((a-d)/b) + omodulo d a b.
  Proof. cbv [omodulo]; pose proof Z.div_mod (a-d) b; lia. Qed.

  Lemma omod_pos_bound d a b : 0 < b -> d <= Z.omodulo d a b < d+b.
  Proof. cbv [Z.omodulo]. Z.to_euclidean_division_equations; lia. Qed.

  Lemma omod_neg_bound d a b : b < 0 -> d+b < Z.omodulo d a b <= d.
  Proof. cbv [Z.omodulo]. Z.to_euclidean_division_equations; lia. Qed.

  Lemma omod_small_iff d a b :
    (d <= a < d+b \/ b = 0 \/ d+b < a <= d) <-> Z.omodulo d a b = a.
  Proof.
    cbv [Z.omodulo]; case (Z.eq_dec b 0) as [->|];
    rewrite ?Zmod_0_r; try pose proof Z.mod_small_iff (a-d) b; lia.
  Qed.

  Lemma omod_small d a b : d <= a < d+b -> Z.omodulo d a b = a.
  Proof. intros; apply omod_small_iff; auto 2. Qed.

  Lemma omod_small_neg d a b : d+b < a <= d -> Z.omodulo d a b = a.
  Proof. intros; apply omod_small_iff; auto 3. Qed.

  Lemma omod_0_r d a : Z.omodulo d a 0 = a.
  Proof. intros; apply omod_small_iff; auto 3. Qed.

  Local Ltac t := cbv [Z.omodulo]; repeat rewrite
    ?Zplus_mod_idemp_l, ?Zplus_mod_idemp_r, ?Zminus_mod_idemp_l, ?Zminus_mod_idemp_r;
    try solve [trivial | lia | f_equal; lia].

  Lemma omod_mod d a b : Z.omodulo d (Z.modulo a b) b = Z.omodulo d a b. Proof. t. Qed.

  Lemma mod_omod d a b : Z.modulo (Z.omodulo d a b) b = Z.modulo a b. Proof. t. Qed.

  Lemma omod_inj_mod d x y m : x mod m = y mod m -> Z.omodulo d x m = Z.omodulo d y m.
  Proof. rewrite <-(omod_mod _ x), <-(omod_mod _ y); congruence. Qed.

  Lemma mod_inj_omod d x y m : Z.omodulo d x m = Z.omodulo d y m -> x mod m = y mod m.
  Proof. rewrite <-(mod_omod d x), <-(mod_omod d y); congruence. Qed.

  Lemma omod_idemp_add d x y m :
    Z.omodulo d (Z.omodulo d x m + Z.omodulo d y m) m = Z.omodulo d (x + y) m.
  Proof. apply omod_inj_mod; rewrite Zplus_mod, !mod_omod, <-Zplus_mod; trivial. Qed.

  Lemma omod_idemp_sub d x y m :
    Z.omodulo d (Z.omodulo d x m - Z.omodulo d y m) m = Z.omodulo d (x - y) m.
  Proof. apply omod_inj_mod; rewrite Zminus_mod, !mod_omod, <-Zminus_mod; trivial. Qed.

  Lemma omod_idemp_mul d x y m :
    Z.omodulo d (Z.omodulo d x m * Z.omodulo d y m) m = Z.omodulo d (x * y) m.
  Proof. apply omod_inj_mod; rewrite Zmult_mod, !mod_omod, <-Zmult_mod; trivial. Qed.


  Definition smodulo a b := Z.omodulo (- Z.quot b 2) a b.

  Lemma div_smod a b : b <> 0 -> a = b * ((a+Z.quot b 2)/b) + Z.smodulo a b.
  Proof.
    cbv [Z.smodulo]; pose proof Z.div_omod (- Z.quot b 2) a b.
    rewrite <-(Z.sub_opp_r a (b ÷ 2)); lia.
  Qed.

  Lemma smod_pos_bound a b: 0 < b -> -b <= 2*Z.smodulo a b < b.
  Proof. cbv [Z.omodulo Z.smodulo]; Z.to_euclidean_division_equations; lia. Qed.

  Lemma smod_neg_bound a b: b < 0 -> b < 2*Z.smodulo a b <= -b.
  Proof. cbv [Z.smodulo Z.omodulo]. Z.to_euclidean_division_equations; lia. Qed.

  Lemma smod_mod a b : Z.smodulo (Z.modulo a b) b = Z.smodulo a b.
  Proof. apply omod_mod. Qed.
  Lemma mod_smod a b : Z.modulo (Z.smodulo a b) b = Z.modulo a b.
  Proof. apply mod_omod. Qed.

  Lemma smod_inj_mod x y m : x mod m = y mod m -> Z.smodulo x m = Z.smodulo y m.
  Proof. apply omod_inj_mod. Qed.

  Lemma mod_inj_smod x y m : Z.smodulo x m = Z.smodulo y m -> x mod m = y mod m.
  Proof. apply mod_inj_omod. Qed.

  Lemma smod_idemp_add x y m :
    Z.smodulo (Z.smodulo x m + Z.smodulo y m) m = Z.smodulo (x + y) m.
  Proof. apply omod_idemp_add. Qed.

  Lemma smod_idemp_sub x y m :
    Z.smodulo (Z.smodulo x m - Z.smodulo y m) m = Z.smodulo (x - y) m.
  Proof. apply omod_idemp_sub. Qed.

  Lemma smod_idemp_mul x y m :
    Z.smodulo (Z.smodulo x m * Z.smodulo y m) m = Z.smodulo (x * y) m.
  Proof. apply omod_idemp_mul. Qed.

  Lemma smod_small_iff a b (d := - Z.quot b 2) :
    (- b <= 2*a - Z.rem b 2 < b \/ b = 0 \/ b < 2*a - Z.rem b 2 <= - b)
    <-> smodulo a b = a.
  Proof.
    pose proof Z.quot_rem b 2 ltac:(lia).
    cbv [smodulo]; pose proof omod_small_iff (- Z.quot b 2) a b; lia.
  Qed.

  Lemma smod_even_small_iff a b (H : Z.rem b 2 = 0) :
    (-b <= 2*a < b \/ b = 0 \/ b < 2*a <= -b) <-> Z.smodulo a b = a.
  Proof. rewrite <-smod_small_iff, H; lia. Qed.

  Lemma smod_small a b : -b <= 2*a - Z.rem b 2 < b -> Z.smodulo a b = a.
  Proof. intros; apply smod_small_iff; auto 2. Qed.

  Lemma smod_even_small a b : Z.rem b 2 = 0 -> -b <= 2*a < b -> Z.smodulo a b = a.
  Proof. intros; apply smod_even_small_iff; auto 2. Qed.

  Lemma smod_small_neg a b : b < 2*a - Z.rem b 2 <= - b -> Z.smodulo a b = a.
  Proof. intros; apply smod_small_iff; auto 3. Qed.

  Lemma smod_even_small_neg a b : Z.rem b 2 = 0 -> b < 2*a <= - b -> Z.smodulo a b = a.
  Proof. intros; apply smod_even_small_iff; auto 3. Qed.

  Lemma smod_0_r a : Z.smodulo a 0 = a.
  Proof. apply Z.omod_0_r. Qed.

  Lemma smod_0_l m : Z.smodulo 0 m = 0.
  Proof. apply smod_small_iff; Z.to_euclidean_division_equations; lia. Qed.

  Lemma smod_idemp_opp x m :
    Z.smodulo (- Z.smodulo x m) m = Z.smodulo (- x) m.
  Proof.
    rewrite <-(Z.sub_0_l x), <-smod_idemp_sub, smod_0_l.
    rewrite (Z.sub_0_l (*workaround*) (smodulo x m)); trivial.
  Qed.
End Z.

(** Alternative conversion function for mapping [Zmod m] to [-m/2, m/2) *)
Definition signed {m} (x : Zmod m) : Z :=
  if N.ltb (N.double x) m then x else x-m.

Lemma smod_unsigned {m} (x : Zmod m) : Z.smodulo (unsigned x) m = signed x.
Proof.
  pose proof to_Z_range x. cbv [signed unsigned Z.smodulo Z.omodulo] in *.
  case (N.ltb_spec (N.double x) m) as []; cycle 1.
  1: erewrite <-Z.mod_add with (b:=-(1)), Z.mul_opp_l by inversion 1.
  all : rewrite Z.mod_small; Z.to_euclidean_division_equations; try lia.
Qed.

Lemma signed_range {m} (x : Zmod m) : -m <= 2*signed x < m.
Proof. rewrite <-smod_unsigned. pose proof Z.smod_pos_bound x m; lia. Qed.

Lemma mod_signed {m} (x : Zmod m) : signed x mod m = unsigned x.
Proof. rewrite <-smod_unsigned, Z.mod_smod, mod_to_Z; trivial. Qed.

Lemma signed_of_Z {m} z : signed (of_Z m z) = Z.smodulo z m.
Proof. rewrite <-smod_unsigned, to_Z_of_Z, Z.smod_mod; trivial. Qed.

Lemma signed_small {m} (x : Zmod m) (H : 2*x < m) : signed x = unsigned x.
Proof.
  pose proof to_Z_range x.
  cbv [signed unsigned] in *; case (N.ltb_spec (N.double x) m) as []; lia.
Qed.

Lemma signed_large {m} (x : Zmod m) (H : m <= 2*x) : signed x = x-m.
Proof.
  pose proof to_Z_range x.
  cbv [signed unsigned] in *; case (N.ltb_spec (N.double x) m) as []; lia.
Qed.

Lemma to_Z_pos {m} (x : Zmod m) (H : 0 <= signed x) : unsigned x = signed x.
Proof.
  pose proof to_Z_range x.
  cbv [signed unsigned] in *. case (N.ltb_spec (N.double x) m) as []; lia.
Qed.

Lemma to_Z_neg {m} (x : Zmod m) (H : signed x < 0) : unsigned x = m + signed x.
Proof.
  pose proof to_Z_range x.
  cbv [signed unsigned] in *. case (N.ltb_spec (N.double x) m) as []; lia.
Qed.

Lemma signed_add {m} x y : signed (@add m x y) = Z.smodulo (signed x+signed y) m.
Proof. rewrite <-!smod_unsigned, to_Z_add, Z.smod_mod, Z.smod_idemp_add; trivial. Qed.

Lemma signed_sub {m} x y : signed (@sub m x y) = Z.smodulo (signed x-signed y) m.
Proof. rewrite <-!smod_unsigned, to_Z_sub, Z.smod_mod, Z.smod_idemp_sub; trivial. Qed.

Lemma signed_opp {m} x : signed (@opp m x) = Z.smodulo (-signed x) m.
Proof. rewrite <-!smod_unsigned, to_Z_opp, Z.smod_mod, Z.smod_idemp_opp; trivial. Qed.

Lemma signed_mul {m} x y : signed (@mul m x y) = Z.smodulo (signed x*signed y) m.
Proof. rewrite <-!smod_unsigned, to_Z_mul, Z.smod_mod, Z.smod_idemp_mul; trivial. Qed.

Module NonuniformDependent.
(** Operations that change the modulus *)

(* This module provides operations that vary m in [Zmod m], for example
 * concatenating bitvectors and combining congruences. *)

(* Effective use of the operations defined here with moduli that are not
   converitble to values requires substantial understanding of dependent types,
   in particular the equality type, the sigma type, and their eliminators. Even
   so, many applications are better served by [Z] or by adopting one
   common-denominator modulus.
   The next few lemmas will give a taste of the challenges. *)

Goal forall {m} (a : Zmod m) {n} (b : Zmod n), Prop.
  intros.
  assert_fails (assert (a = b)). (* type error: need n == m *)
  assert_fails (pose (add a b)). (* type error: need n == m *)
Abort.

Lemma to_N_inj_dep {m} (a : Zmod m) {n} (b : Zmod n) :
  m = n -> to_N a = to_N b -> existT _ _ a = existT _ _ b.
Proof. destruct 1; auto using f_equal, to_N_inj. Qed.

Lemma to_N_eq_rect {m} (a : Zmod m) n p : to_N (eq_rect _ _ a n p) = to_N a.
Proof. case p; trivial. Qed.

Lemma to_N_eq_rect_attempt {m} (a : Zmod m) n p : to_N (eq_rect (Zmod m) id a (Zmod n) p) = to_N a.
Proof. assert_fails (case p). Abort.

Lemma to_Z_eq_rect {m} (a : Zmod m) n p : to_Z (eq_rect _ _ a n p) = to_Z a.
Proof. case p; trivial. Qed.

Lemma to_Z_inj_dep {m} (a : Zmod m) {n} (b : Zmod n) :
  m = n -> to_Z a = to_Z b -> existT _ _ a = existT _ _ b.
Proof. destruct 1; auto using f_equal, to_Z_inj. Qed.

Module Import NNN. Module N.
  Local Open Scope N_scope.

  Definition undivmod b hi lo := b*hi + lo.

  Lemma div_undivmod b hi lo (H : lo < b) : N.div (undivmod b hi lo) b = hi.
  Proof. cbv [undivmod]. zify; Z.div_mod_to_equations; nia. Qed.

  Lemma mod_undivmod b hi lo (H : lo < b) : N.modulo (undivmod b hi lo) b = lo.
  Proof.
    cbv [undivmod]; rewrite N.add_comm, N.mul_comm,  N.Div0.mod_add, N.mod_small; trivial.
  Qed.

  Lemma undivmod_pow2 w hi lo (H : lo < 2^w) :
    N.undivmod (2^w) hi lo = N.lor (N.shiftl hi w) lo.
  Proof.
    cbv [N.undivmod]. enough (N.land (N.shiftl hi w) lo = 0).
    { rewrite <-N.lxor_lor, <-N.add_nocarry_lxor, N.shiftl_mul_pow2; lia. }
    rewrite <-(N.mod_small _ _ H).
    apply N.bits_inj_0; intros i; rewrite ?N.land_spec.
    case (N.ltb_spec i w) as [].
    all : rewrite ?N.shiftl_spec_low, ?N.shiftl_spec_high, ?N.mod_pow2_bits_high by lia.
    all : rewrite ?Bool.andb_false_l, ?Bool.andb_false_r; trivial.
  Qed.
End N. End NNN.

(* TODO: high part first or low part first? *)
Definition undivmodM {a b} (hi : Zmod a) (lo : Zmod b) : Zmod (a * b).
  refine (of_small_N _ (N.undivmod b hi lo) (fun _ => _))%N.
  abstract (cbv [N.undivmod]; pose proof to_N_range hi; pose proof to_N_range lo; nia).
Defined.

Lemma undivmodM_ok {a b} hi lo : @undivmodM a b hi lo = of_N _ (N.undivmod b hi lo).
Proof. apply of_small_N_ok. Qed.

Lemma to_N_undivmodM {a b} hi lo : to_N (@undivmodM a b hi lo) = N.undivmod b hi lo.
Proof. apply to_N_of_small_N. Qed.

Lemma to_Z_undivmodM {a b} hi lo : to_Z (@undivmodM a b hi lo) = b*hi + lo.
Proof. cbv [to_Z]. rewrite to_N_undivmodM. cbv [N.undivmod]. lia. Qed.

Definition divM a b (x : Zmod (a * b)) : Zmod a.
  refine (of_small_N _ (x / b) (fun _ => _))%N.
  abstract (pose proof to_N_range x; zify; Z.div_mod_to_equations; nia).
Defined.

Lemma divM_ok {a b} x : @divM a b x = of_N _ (x / b)%N.
Proof. apply of_small_N_ok. Qed.

Lemma to_N_divM {a b} x : to_N (@divM a b x) = (x / b)%N.
Proof. apply to_N_of_small_N. Qed.

Lemma divM_undivmodM {a b} x y : divM a b (undivmodM x y) = x.
Proof.
  apply to_N_inj. rewrite to_N_divM, to_N_undivmodM, N.div_undivmod;
    auto using to_N_range.
Qed.

Definition modM a b (x : Zmod (a * b)) := of_N b x.

Lemma modM_ok {a b} x : @modM a b x = of_N _ (x mod b)%N.
Proof. apply of_small_N_ok. Qed.

Lemma to_N_modM {a b} x : to_N (@modM a b x) = (x mod b)%N.
Proof. apply to_N_of_small_N. Qed.

Lemma modM_undivmodM {a b} x y : modM a b (undivmodM x y) = y.
Proof.
  apply to_N_inj. rewrite to_N_modM, to_N_undivmodM, N.mod_undivmod;
    auto using to_N_range.
Qed.

Definition crtM {a b} (x : Zmod a) (y : Zmod b) := of_Z (a*b) (solvecong a b x y).

Lemma modM_crtM {a b : positive} x y (H : Z.gcd a b = 1) : modM a b (crtM x y) = y.
Proof.
  apply to_Z_inj; cbv [crtM modM].
  rewrite to_N_of_Z, to_Z_of_N, Z2N.id, <-Zmod_div_mod; try lia.
  { rewrite (proj2 (solvecong_coprime a b x y H)), mod_to_Z; trivial. }
  { exists a. lia. }
  { apply Z.mod_pos_bound. lia. }
Qed.

Lemma crtM_comm {a b} (x : Zmod a) (y : Zmod b) (H : Z.gcd a b = 1) :
  existT Zmod _ (crtM x y) = existT Zmod _ (crtM y x).
Proof.
  apply to_Z_inj_dep; try lia; cbv [crtM]; rewrite !to_Z_of_Z.
  rewrite solvecong_comm; f_equal; try lia.
Qed.

Module Import PPos.
Module Pos.
  Lemma pow_add_r (a b c : positive) : (a^(b+c) = a^b * a^c)%positive.
  Proof.
    enough (N.pos (a ^ (b + c)) = N.pos (a ^ b * a ^ c)) by lia.
    rewrite <-(positive_nat_N (Pos.pow _ _)), Pos2Nat.inj_pow, Nat2N.inj_pow, 2positive_nat_N.
    replace (N.pos (b+c)) with (N.pos b + N.pos c)%N by lia; rewrite N.pow_add_r; lia.
  Qed.
End Pos.
End PPos.

Definition concatM {a b} (hi : Zmod (2^a)) (lo : Zmod (2^b)) : Zmod (2^(a+b)).
  refine (of_small_N _ (N.lor (N.shiftl hi b) lo) (fun _ => _))%N.
  abstract (
    rewrite <-N.undivmod_pow2, Pos.pow_add_r by auto using to_N_range;
    cbv [N.undivmod]; pose proof to_N_range hi; pose proof to_N_range lo; nia).
Defined.

Lemma concatM_ok {a b} hi lo : to_N (@concatM a b hi lo) = to_N (undivmodM hi lo).
Proof.
  cbv [concatM]; rewrite to_N_of_small_N, to_N_undivmodM.
  rewrite <-N.undivmod_pow2 by auto using to_N_range; trivial.
Qed.

Lemma concatM_ok_dep {a b} hi lo : existT _ _ (@concatM a b hi lo) = existT _ _ (undivmodM hi lo).
Proof. apply to_N_inj_dep; auto using concatM_ok, Pos.pow_add_r. Qed.

End NonuniformDependent.

(** Optimized conversions and operations for m=2^w *)
(* TODO: move to some ZArith file *)
Module Import PPPos.
Module Pos.
Definition ones (p : positive) : positive :=
  N.iter (Pos.pred_N p) (fun n => n~1)%positive xH.
End Pos.
End PPPos.
Module Import NNN.
Module N.
Lemma ones_succ n (H : N.le 0 n) : N.ones (N.succ n) = N.succ_double (N.ones n).
Proof. rewrite 2N.ones_equiv, N.pow_succ_r; lia. Qed.

Lemma pos_ones p : N.pos (Pos.ones p) = N.ones (N.pos p).
Proof.
  cbv [Pos.ones]. set (fun n => _) as step.
  replace (N.pos p) with (N.succ (Pos.pred_N p)) by lia.
  induction (Pos.pred_N p) using N.peano_ind; trivial.
  rewrite N.ones_succ, <-IHn by lia; clear IHn.
  rewrite N.iter_succ. rewrite N.succ_double_spec; trivial.
Qed.
End N.
End NNN.
Module Import ZZ.
Module Z.
Lemma ones_succ n (H : Z.le 0 n) : Z.ones (Z.succ n) = Z.succ_double (Z.ones n).
Proof. rewrite 2Z.ones_equiv, Z.pow_succ_r; lia. Qed.

Lemma pos_ones p : Z.pos (Pos.ones p) = Z.ones (Z.pos p).
Proof.
  cbv [Pos.ones]. set (fun n => _) as step.
  replace (Z.pos p) with (Z.succ (Z.of_N (Pos.pred_N p))) by lia.
  induction (Pos.pred_N p) using N.peano_ind; trivial.
  rewrite Z.ones_succ, N2Z.inj_succ, <-IHn by lia; clear IHn.
  rewrite N.iter_succ. rewrite Pos2Z.pos_xI, Z.succ_double_spec; trivial.
Qed.
End Z.
End ZZ.

Local Open Scope Zmod_scope.

Definition of_N_pow2 (w : positive) (n : N) : Zmod (2^w).
Proof.
  refine (of_small_N _ (N.land n (Pos.ones w)) (fun _ => _)).
  abstract (rewrite N.pos_ones, N.land_ones; apply N.mod_upper_bound; discriminate).
Defined.

Lemma of_N_pow2_ok {w} n : of_N_pow2 w n = of_N (2^w) n.
Proof.
  cbv [of_N_pow2]. apply to_N_inj. rewrite of_small_N_ok, !to_N_of_N.
  rewrite N.pos_ones, N.land_ones, N.Div0.mod_mod; trivial; discriminate.
Qed.

Definition of_Z_pow2 (w : positive) (z : Z) : Zmod (2^w).
  refine (of_small_Z _ (Z.land z (Pos.ones w)) (fun _ => _)).
  abstract (rewrite Z.pos_ones, Z.land_ones; Z.div_mod_to_equations; lia).
Defined.

Lemma of_Z_pow2_ok {w} z : of_Z_pow2 w z = of_Z (2^w) z.
Proof.
  cbv [of_Z_pow2]. apply to_N_inj. rewrite of_small_Z_ok, !to_N_of_Z.
  rewrite Z.pos_ones, Z.land_ones, Pos2Z.inj_pow, Z.mod_mod; lia.
Qed.

Definition mul_pow2 {w} (x y : Zmod (2^w)) : Zmod (2^w) := of_N_pow2 w (x * y).

Lemma mul_pow2_ok {w} (x y : Zmod (2^w)) : mul_pow2 x y = mul x y.
Proof. apply of_N_pow2_ok. Qed.

(* TODO: connect to Fin.t *)

(** Tests *)

Goal True. unify (add (of_N_value 4 3 I) (of_Z_pow2 2 1)) (of_Z 4 0). Abort.
Goal True. pose (((of_N_value 4 3 I) - (of_Z_pow2 2 1) + of_Z _ 2)). cbv in z. Abort.
Add Ring ring_Zmod2 : (@ring_theory 2).
Add Ring ring_Zmod2p1 : (@ring_theory (2^1)).
Goal True. assert (one - one = zero :> Zmod 2) as _ by ring. Abort.
Goal True. assert (of_Z _ 1 - of_Z _ 1 = zero :> Zmod (2^1)) as _ by ring. Abort.

Goal pow_N (of_Z (2^127-1) 2) (2^127-3) =? inv (of_Z (2^127-1) 2) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
