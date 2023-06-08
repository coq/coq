Require Import Coq.Numbers.Zmod.TODO_MOVE.
Require Import Coq.Bool.Bool.

Require Import Coq.NArith.NArith Coq.ZArith.ZArith Coq.micromega.Lia.
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

Lemma mod_to_N {m} (x : Zmod m) : (to_N x mod (N.pos m))%N = to_N x.
Proof. rewrite N.mod_small; auto using to_N_range. Qed.

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

Lemma of_N_mod {m} x : of_N m (x mod N.pos m) = of_N m x.
Proof. apply to_N_inj. rewrite ?to_N_of_N, ?N.Div0.mod_mod; trivial. Qed.

(** Conversions to nat *)

Definition of_nat m (a : nat) := of_N m (N.of_nat a).
Definition to_nat {m} (a : Zmod m) := N.to_nat (to_N a).

Lemma of_nat_to_nat {m} a : of_nat m (to_nat a) = a.
Proof. cbv [of_nat to_nat]. rewrite N2Nat.id, of_N_to_N; trivial. Qed.

Lemma to_N_of_nat {m} a : to_N (of_nat m a) = N.modulo (N.of_nat a) (N.pos m).
Proof. cbv [of_nat to_nat]. rewrite to_N_of_N; trivial. Qed.

Lemma to_nat_of_nat {m} a : to_nat (of_nat m a) = Nat.modulo a (Pos.to_nat m).
Proof.  cbv [to_nat]. rewrite to_N_of_nat, N2Nat.inj_mod, Nat2N.id, positive_N_nat; trivial. Qed.

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

Lemma of_Z_mod {m} x : of_Z m (x mod Z.pos m) = of_Z m x.
Proof. apply to_Z_inj. rewrite ?to_Z_of_Z, ?Z.mod_mod; lia. Qed.

(* Converting N<->Z through Zmod *)

Lemma to_Z_of_N_value {m} n pf : to_Z (of_N_value m n pf) = Z.of_N n. Proof. trivial. Qed.

Lemma to_Z_of_small_N {m} n pf : to_Z (of_small_N m n pf) = Z.of_N n. Proof. trivial. Qed.

Lemma to_Z_of_N {m} n : to_Z (of_N m n) = (Z.of_N n) mod (Z.pos m).
Proof. cbv [to_Z]. rewrite to_N_of_N, N2Z.inj_mod; trivial. Qed.

Lemma to_N_of_Z {m} z : to_N (of_Z m z) = Z.to_N (z mod (Z.pos m)).
Proof. trivial. Qed.

(* Converting nat<->Z through Zmod *)

Lemma to_Z_of_nat {m} a : to_Z (of_nat m a) = Z.modulo (Z.of_nat a) (Z.pos m).
Proof. cbv [to_Z]; rewrite to_N_of_nat, N2Z.inj_mod, nat_N_Z; trivial. Qed.

Module Import Coercions.
  Coercion Z.pos : positive >-> Z.
  Coercion N.pos : positive >-> N.
  Coercion Z.of_N : N >-> Z.
  Coercion to_Z : Zmod >-> Z.
  Coercion to_N : Zmod >-> N.
End Coercions.
Local Set Printing Coercions.

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

Lemma signed_inj m (x y : Zmod m) : signed x = signed y -> x = y.
Proof.
  rewrite <-2 smod_unsigned; intros H%Z.mod_inj_smod; rewrite ?mod_to_Z in *.
  apply to_Z_inj, H.
Qed.

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

(** Constants *)
Notation zero := (of_N_value _ 0 I).
Notation one := (of_N _ 1).
Lemma to_N_0 {m} : @to_N m zero = 0%N. Proof. trivial. Qed.
Lemma to_Z_0 {m} : @to_Z m zero = 0. Proof. trivial. Qed.
Lemma signed_0 {m} : @signed m zero = 0. Proof. trivial. Qed.
Lemma of_Z_0 {m} : of_Z m 0 = zero. Proof. trivial. Qed.
Lemma of_N_0 {m} : of_N m 0 = zero. Proof. trivial. Qed.
Lemma of_N_1 {m} : of_N m 1 = one. Proof. trivial. Qed.
Lemma of_Z_1 {m} : of_Z m 1 = one.
Proof. apply to_Z_inj. rewrite to_Z_of_Z, to_Z_of_N; trivial. Qed.

Lemma of_N_nz {m} x (H : (x mod N.pos m <> 0)%N) : of_N m x <> zero.
Proof.
  intro Hx. apply (f_equal to_N) in Hx. rewrite to_N_of_N, to_N_0 in Hx; contradiction.
Qed.

Lemma of_Z_nz {m} x (H : (x mod Z.pos m <> 0)%Z) : of_Z m x <> zero.
Proof.
  intro Hx. apply (f_equal to_Z) in Hx. rewrite to_Z_of_Z, to_Z_0 in Hx; contradiction.
Qed.

Definition elements m : list (Zmod m) := List.map (of_nat m) (List.seq 0 (Pos.to_nat m)).

Lemma length_elements m : length (elements m) = Pos.to_nat m.
Proof. cbv [elements]. rewrite List.map_length, List.seq_length; trivial. Qed.

Lemma nth_error_elements {m} n : List.nth_error (elements m) n =
  if (Nat.ltb n (Pos.to_nat m)) then Some (of_nat _ n) else None.
Proof.
  cbv [elements].
  rewrite List.nth_error_map, List.nth_error_seq.
  case Nat.ltb; trivial.
Qed.

Definition in_elements {m} a : List.In a (elements m).
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

Lemma signed_add {m} x y : signed (@add m x y) = Z.smodulo (signed x+signed y) m.
Proof. rewrite <-!smod_unsigned, to_Z_add, Z.smod_mod, Z.smod_idemp_add; trivial. Qed.

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

Lemma signed_sub {m} x y : signed (@sub m x y) = Z.smodulo (signed x-signed y) m.
Proof. rewrite <-!smod_unsigned, to_Z_sub, Z.smod_mod, Z.smod_idemp_sub; trivial. Qed.

Lemma to_N_sub {m} (x y : Zmod m) : to_N (sub x y) = Z.to_N ((to_N x - to_N y) mod m).
Proof.
  pose proof to_Z_sub x y.
  pose proof to_Z_range (sub x y).
  cbv [to_Z] in *; lia.
Qed.

Definition opp {m} (x : Zmod m) : Zmod m := sub zero x.

Lemma to_Z_opp {m} (x : Zmod m) : to_Z (opp x) = (- to_Z x) mod m.
Proof. apply to_Z_sub. Qed.

Lemma signed_opp {m} x : signed (@opp m x) = Z.smodulo (-signed x) m.
Proof. rewrite <-!smod_unsigned, to_Z_opp, Z.smod_mod, Z.smod_idemp_opp; trivial. Qed.

Lemma to_N_opp {m} (x : Zmod m) : to_N (opp x) = Z.to_N ((- to_N x) mod m).
Proof. apply to_N_sub. Qed.

Definition mul {m} (x y : Zmod m) : Zmod m := of_N m (to_N x * to_N y).

Lemma to_N_mul {m} (x y : Zmod m) : to_N (mul x y) = ((to_N x * to_N y) mod m)%N.
Proof. cbv [mul]; rewrite ?to_N_of_Z; trivial. Qed.

Lemma to_Z_mul {m} (x y : Zmod m) : to_Z (mul x y) = (to_Z x * to_Z y) mod m.
Proof. cbv [to_Z]. rewrite to_N_mul, N2Z.inj_mod; lia. Qed.

Lemma signed_mul {m} x y : signed (@mul m x y) = Z.smodulo (signed x*signed y) m.
Proof. rewrite <-!smod_unsigned, to_Z_mul, Z.smod_mod, Z.smod_idemp_mul; trivial. Qed.

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

(* TODO: high half of signed and unsigned multiplication? *)

(** Three notions of division *)
(* TODO: udiv vs divu, etc *)

Definition udiv {m} (x y : Zmod m) : Zmod m.
  refine (of_small_N m (N.div x y) (fun _ => _)).
  abstract (pose proof to_N_range x; zify; Z.to_euclidean_division_equations; nia).
Defined.

Lemma to_N_udiv {m} x y : to_N (@udiv m x y) = N.div x y.
Proof. apply to_N_of_small_N. Qed.

Lemma udiv_0_r {m} x : @udiv m x zero = zero.
Proof. cbv [udiv]. apply to_N_inj. rewrite to_N_of_small_N, to_N_0, N.div_0_r; trivial. Qed.

Lemma to_Z_udiv {m} x y : to_Z (@udiv m x y) = Z.div x y.
Proof. cbv [udiv]. rewrite to_Z_of_small_N, N2Z.inj_div; trivial. Qed.

Definition sdiv {m} (x y : Zmod m) := of_Z m (Z.div (signed x) (signed y)).

Lemma signed_sdiv {m} x y : @signed m (sdiv x y) = Z.smodulo (signed x / signed y) m.
Proof. apply signed_of_Z. Qed.

Lemma sdiv_0_r {m} x : @sdiv m x zero = zero.
Proof. cbv [sdiv]. apply to_Z_inj; rewrite to_Z_of_Z, signed_0, Zdiv_0_r; trivial. Qed.

Lemma signed_sdiv_small {m : positive} x y :
  not (signed x = -m/2 /\ signed y = -1 /\ m mod 2 = 0) ->
  @signed m (sdiv x y) = signed x / signed y.
Proof.
  intros H; rewrite signed_sdiv; apply Z.smod_small.
  pose proof signed_range x; pose proof signed_range y.
  Z.to_euclidean_division_equations; nia.
Qed.

Lemma sdiv_overflow {m : positive} x y
  (Hm : m mod 2 = 0) (Hx : signed x = -m/2) (Hy : signed y = -1) :
  @sdiv m x y = x.
Proof.
  apply signed_inj; rewrite signed_sdiv, Hx, Hy.
  change (-1) with (-(1)); rewrite Z_div_zero_opp_full, Z.div_opp_opp, Z.div_1_r by lia.
  rewrite <-Z.smod_mod, <-Z.mod_add with (b:=-1), Z.smod_mod by lia.
  rewrite Z.smod_even_small; Z.to_euclidean_division_equations; nia.
Qed.

Definition inv {m} (x : Zmod m) : Zmod m := of_Z m (Znumtheory.invmod (to_Z x) m).

Lemma to_Z_inv {m} x : to_Z (@inv m x) = Znumtheory.invmod x m mod m.
Proof. apply to_Z_of_Z. Qed.

Lemma inv_0 {m} : @inv m zero = zero. Proof. trivial. Qed.

Definition ndiv {m} (x y : Zmod m) : Zmod m := mul x (inv y).

Lemma to_Z_ndiv {m} x y : to_Z (@ndiv m x y) = x * Znumtheory.invmod y m mod m.
Proof. cbv [ndiv]. rewrite to_Z_mul, to_Z_inv, Z.mul_mod_idemp_r; lia. Qed.

Lemma ndiv_0_r {m} x : @ndiv m x zero = zero.
Proof. cbv [ndiv]. rewrite inv_0, mul_0_r; trivial. Qed.

Lemma mul_inv_l {m} x y : mul (@inv m y) x = ndiv x y.
Proof. apply to_Z_inj. cbv [ndiv inv]. rewrite mul_comm; trivial. Qed.

Lemma mul_inv_r {m} x y : mul x (@inv m y) = ndiv x y.
Proof. rewrite mul_comm, mul_inv_l; trivial. Qed.

(* TODO: quotient and remainder? *)

(**  Powers  *)

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

Lemma of_N_powmod {m} x n : of_N m (x ^ n mod m) = pow_N (of_N m x) n.
Proof. apply to_N_inj; rewrite ?to_N_pow_N, ?to_N_of_N, ?N.mod_pow_l, ?N.Div0.mod_mod; trivial. Qed.

Lemma of_N_pow {m} x n : of_N m (x ^ n) = pow_N (of_N m x) n.
Proof. rewrite <-of_N_powmod, of_N_mod; trivial. Qed.

Lemma of_Z_pow {m} x n (Hn : 0 <= n) : of_Z m (x ^ n) = pow_N (of_Z m x) (Z.to_N n).
Proof.
  apply to_N_inj.
  rewrite to_N_pow_N, 2to_N_of_Z, <-Z.mod_pow_l, <-Z2N.inj_pow, Z2N.inj_mod;
  trivial; try eapply Z.pow_nonneg; (Z.div_mod_to_equations; lia).
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

Lemma pow_N_mul_r {m} (x : Zmod m) a b : pow_N x (a*b) = pow_N (pow_N x a) b.
Proof. apply to_N_inj; rewrite ?to_N_pow_N, ?N.pow_mul_r, ?N.mod_pow_l; trivial. Qed.

Lemma pow_N_mul_l {m} (x y : Zmod m) n : pow_N (mul x y) n = mul (pow_N x n) (pow_N y n).
Proof.
  apply to_N_inj; pose proof N.Div0.mul_mod.
  rewrite ?to_N_pow_N, ?to_N_mul, ?N.mod_pow_l, ?N.pow_mul_l, ?to_N_pow_N; auto.
Qed.

(** Bitwise operations *)

Definition xor {m} (x y : Zmod m) := of_N m (N.lxor x y).

Definition or {m} (x y : Zmod m) := of_N m (N.lor x y).

Definition not {m} (x : Zmod m) := of_Z m (Z.lnot (to_Z x)).

Definition and {m} (x y : Zmod m) : Zmod m.
  refine (of_small_N m (N.land x y) (fun _ => _)).
  abstract (pose proof to_N_range x; pose proof N.land_mono x y; lia).
Defined.

Definition ndn {m} (x y : Zmod m) : Zmod m.
  refine (of_small_N m (N.ldiff x y) (fun _ => _)).
  abstract (pose proof to_N_range x; pose proof N.ldiff_mono x y; lia).
Defined.

(* To N *)

Lemma Ntestbit_high_pow2 {w} (x : Zmod (2^w)) i (Hi : (w <= i)%N) : N.testbit x i = false.
Proof. rewrite <-mod_to_N, ?N.pos_pow, N.mod_pow2_bits_high; trivial. Qed.

Lemma to_N_xor_pow2 {w} x y : @to_N (2^w) (xor x y) = N.lxor x y.
Proof.
  cbv [xor]; rewrite to_N_of_N; apply N.bits_inj; intros i; destruct (N.ltb_spec i w);
  repeat rewrite ?N.pos_pow, ?N.lxor_spec, ?N.mod_pow2_bits_low, ?N.mod_pow2_bits_high, ?Ntestbit_high_pow2 by trivial; trivial.
Qed.

Lemma to_N_or_pow2 {w} x y : @to_N (2^w) (or x y) = N.lor x y.
Proof.
  cbv [or]; rewrite to_N_of_N; apply N.bits_inj; intros i; destruct (N.ltb_spec i w);
  repeat rewrite ?N.pos_pow, ?N.lor_spec, ?N.mod_pow2_bits_low, ?N.mod_pow2_bits_high, ?Ntestbit_high_pow2 by trivial; trivial.
Qed.

Lemma to_N_not {w} x : @to_N (2^w) (not x) = N.lnot x w.
Proof.
  cbv [not]; rewrite to_N_of_Z, ?Pos2Z.inj_pow; apply N.bits_inj; intro i.
  rewrite <-Z.testbit_of_N, Z2N.id by (apply Z.mod_pos_bound; lia).
  destruct (N.ltb_spec i w);
  repeat rewrite
    ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high, ?Z.lnot_spec, ?Ntestbit_high_pow2,
    ?N.mod_pow2_bits_low, ?N.mod_pow2_bits_high, ?N.lnot_spec_low, ?N.lnot_spec_high
    by lia; trivial.
  cbv [to_Z]; rewrite Z.testbit_of_N; trivial.
Qed.

Lemma to_N_and {m} x y : @to_N m (and x y) = N.land x y.
Proof. apply to_N_of_small_N. Qed.

Lemma to_N_ndn {m} x y : @to_N m (ndn x y) = N.ldiff x y.
Proof. apply to_N_of_small_N. Qed.

(** Shifts *)

Definition sru_N {m} (x : Zmod m) (n : N) : Zmod m.
  refine (of_small_N m (N.shiftr x n) (fun _ => _)).
  abstract (pose (to_N_range x); pose (N.shiftr_mono x n); lia).
Defined.

Definition srs_N {m} x (n : N) := of_Z m (Z.shiftr (@signed m x) n).

Definition slu_N {m} x n := of_N m (N.shiftl x n).

Lemma to_N_sru_N {m} x n : @to_N m (sru_N x n) = N.shiftr x n.
Proof. apply to_N_of_small_N. Qed.

Lemma to_Z_sru_N {m} x n : @to_Z m (sru_N x n) = Z.shiftr x n.
Proof. cbv [to_Z]. rewrite to_N_sru_N, N2Z.inj_shiftr; trivial. Qed.

Lemma signed_srs_N {m} x n : @signed m (srs_N x n) = Z.shiftr (signed x) n.
Proof.
  cbv [srs_N]; rewrite signed_of_Z; apply Z.smod_small.
  rewrite Z.shiftr_div_pow2 by lia; pose proof signed_range x.
  Z.to_euclidean_division_equations; nia.
Qed.

Lemma to_Z_srs_N {m} x n : @to_Z m (srs_N x n) = Z.shiftr (signed x) n mod m.
Proof. rewrite <-mod_to_Z, <-Z.mod_smod, <-signed_srs_N, <-signed_of_Z, of_Z_to_Z; trivial. Qed.

Lemma to_N_slu_N {m} x n : @to_N m (slu_N x n) = (N.shiftl x n mod m)%N.
Proof. cbv [slu_N]; rewrite to_N_of_N; trivial. Qed.

Lemma to_Z_slu_N {m} x n : @to_Z m (slu_N x n) = Z.shiftl x n mod m.
Proof. cbv [slu_N]; rewrite to_Z_of_N, N2Z.inj_shiftl; trivial. Qed.

(** Shifts by [Zmod] *)
(* Note: some systems truncate the shift amount first *)

Definition sru {m} (x y : Zmod m) := @sru_N m x y.
Definition slu {m} (x y : Zmod m) := @slu_N m x y.
Definition srs {m} (x y : Zmod m) := @srs_N m x y.

(* To Z *)

Lemma testbit_high_pow2 {w} (x : Zmod (2^w)) i (Hi : (w <= i)) : Z.testbit x i = false.
Proof. cbv [to_Z]. rewrite Z.testbit_of_N', Ntestbit_high_pow2; trivial; lia. Qed.

Lemma to_Z_xor_pow2 {w} x y : @to_Z (2^w) (xor x y) = Z.lxor x y.
Proof. cbv [to_Z]. rewrite to_N_xor_pow2, N2Z.inj_lxor; trivial. Qed.

Lemma to_Z_or_pow2 {w} x y : @to_Z (2^w) (or x y) = Z.lor x y.
Proof. cbv [to_Z]. rewrite to_N_or_pow2, N2Z.inj_lor; trivial. Qed.

Lemma to_Z_not {w} x : @to_Z (2^w) (not x) = Z.lnot x mod 2^w.
Proof.
  cbv [not]; rewrite to_Z_of_Z, ?Pos2Z.inj_pow; apply Z.bits_inj'; intros i Hi.
  destruct (Z.ltb_spec i w);
  repeat rewrite ?Z.lnot_spec, ?testbit_high_pow2 by lia; trivial.
Qed.

Lemma to_Z_and {m} x y : @to_Z m (and x y) = Z.land x y.
Proof. cbv [to_Z]. rewrite to_N_and, N2Z.inj_land; trivial. Qed.

Lemma to_Z_ndn {m} x y : @to_Z m (ndn x y) = Z.ldiff x y.
Proof. cbv [to_Z]. rewrite to_N_ndn, N2Z.inj_ldiff; trivial. Qed.

(** Misc *)

Lemma to_N_1 {m : positive} (Hm : 2 <= m) : @to_N m one = 1%N.
Proof. rewrite to_N_of_N, N.mod_small; lia. Qed.

Lemma to_Z_1 {m : positive} (Hm : 2 <= m) : @to_Z m one = 1.
Proof. rewrite to_Z_of_N, Z.mod_small; lia. Qed.

Lemma to_N_nz {m} (x : Zmod m) (H : x <> zero) : to_N x <> 0%N.
Proof. intros X; apply H, to_N_inj. rewrite X; trivial. Qed.

Lemma to_Z_nz {m} (x : Zmod m) (H : x <> zero) : to_Z x <> 0.
Proof. intros X; apply H, to_Z_inj. rewrite X; trivial. Qed.

Lemma one_neq_zero {m : positive} (Hm : 2 <= m) : one <> zero :> Zmod m.
Proof.
  intro H. apply (f_equal to_N) in H.
  rewrite to_N_1, to_N_0 in H; lia.
Qed.

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

Lemma chinese_remainder_solvecong_Zmod
  (a b : positive) (H : Z.gcd a b = 1) (x : Zmod a) (y : Zmod b)
  z (Hx : z mod a = x) (Hy : z mod b = y) :
  of_Z _ z = of_Z _ (Znumtheory.solvecong a b x y) :> Zmod (a*b).
Proof.
  apply to_Z_inj; rewrite !to_Z_of_Z, !Pos2Z.inj_mul.
  apply Znumtheory.chinese_remainder_solvecong;
    rewrite ?Hx, ?Hy, ?mod_to_Z; trivial; inversion 1.
Qed.

Module Import Notations.
  Declare Scope Zmod_scope.
  Delimit Scope Zmod_scope with Zmod.
  (* Bind Scope Zmod_scope with Zmod. *)
  Infix "*" := mul : Zmod_scope.
  Infix "+" := add : Zmod_scope.
  Infix "-" := sub : Zmod_scope.
  Infix "=?" := eqb : Zmod_scope.
  Notation "- x" := (opp x) : Zmod_scope.
End Notations.
