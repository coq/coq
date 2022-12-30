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

(* TODO: move *)
Module Z.
  Definition smodulo a b := Z.modulo (a + Z.quot b 2) b - Z.quot b 2.

  Lemma smod_0_l m : Z.smodulo 0 m = 0.
  Proof.
    cbv [Z.smodulo].
    rewrite Z.add_0_l; apply Z.sub_move_0_r.
    case (Z.eq_dec m 0) as []; try (Z.to_euclidean_division_equations; lia).
    apply Z.mod_small_iff; Z.to_euclidean_division_equations; lia.
  Qed.

  Local Ltac t := cbv [Z.smodulo];
    repeat rewrite  ?Zplus_mod_idemp_l, ?Zplus_mod_idemp_r,
                    ?Zminus_mod_idemp_l, ?Zminus_mod_idemp_r,
                    ?Zmult_mod_idemp_l,  ?Zmult_mod_idemp_r;
    try solve [trivial | lia | f_equal; lia].

  Lemma smod_mod a b : Z.smodulo (Z.modulo a b) b = Z.smodulo a b. Proof. t. Qed.
  Lemma mod_smod a b : Z.modulo (Z.smodulo a b) b = Z.modulo a b. Proof. t. Qed.

  Lemma smod_inj_mod x y m : x mod m = y mod m -> Z.smodulo x m = Z.smodulo y m.
  Proof. rewrite <-(smod_mod x), <-(smod_mod y); congruence. Qed.

  Lemma mod_inj_smod x y m : Z.smodulo x m = Z.smodulo y m -> x mod m = y mod m.
  Proof. rewrite <-(mod_smod x), <-(mod_smod y); congruence. Qed.

  Lemma smod_idemp_add x y m :
    Z.smodulo (Z.smodulo x m + Z.smodulo y m) m = Z.smodulo (x + y) m.
  Proof. apply smod_inj_mod; rewrite Zplus_mod, !mod_smod, <-Zplus_mod; trivial. Qed.

  Lemma smod_idemp_sub x y m :
    Z.smodulo (Z.smodulo x m - Z.smodulo y m) m = Z.smodulo (x - y) m.
  Proof. apply smod_inj_mod; rewrite Zminus_mod, !mod_smod, <-Zminus_mod; trivial. Qed.

  Lemma smod_idemp_mul x y m :
    Z.smodulo (Z.smodulo x m * Z.smodulo y m) m = Z.smodulo (x * y) m.
  Proof. apply smod_inj_mod; rewrite Zmult_mod, !mod_smod, <-Zmult_mod; trivial. Qed.

  Lemma smod_idemp_opp x m :
    Z.smodulo (- Z.smodulo x m) m = Z.smodulo (- x) m.
  Proof.
    rewrite <-(Z.sub_0_l x), <-smod_idemp_sub, smod_0_l.
    rewrite (Z.sub_0_l (smodulo x m)); trivial.
  Qed.

  Lemma smod_neg_bound a b: b < 0 -> b < 2*Z.smodulo a b <= -b.
  Proof. cbv [Z.smodulo]; Z.to_euclidean_division_equations; lia. Qed.

  Lemma smod_pos_bound a b: 0 < b -> -b <= 2*Z.smodulo a b < b.
  Proof. cbv [Z.smodulo]; Z.to_euclidean_division_equations; lia. Qed.
End Z.

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

Definition of_N (m : positive) (n : N) : Zmod m.
  refine (of_small_N m (n mod (N.pos m)) (fun _ => _)).
  abstract (apply N.mod_upper_bound; discriminate).
Defined.

Lemma of_small_N_ok {m} n pf : of_small_N m n pf = of_N m n.
Proof. apply to_N_inj; apply eq_sym, N.mod_small, pf, I. Qed.

Lemma to_N_of_N {m} n : to_N (of_N m n) = (n mod (N.pos m))%N.
Proof. trivial. Qed.

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

(** Operations *)
Notation zero := (of_N_value _ 0 I).
Notation one := (of_N _ 1).
Lemma to_N_0 {m} : @to_N m zero = 0%N. Proof. trivial. Qed.
Lemma to_Z_0 {m} : @to_Z m zero = 0. Proof. trivial. Qed.
Lemma of_Z_0 {m} : of_Z m 0 = zero. Proof. trivial. Qed.
Lemma of_N_0 {m} : of_N m 0 = zero. Proof. trivial. Qed.
Lemma of_N_1 {m} : of_N m 1 = one. Proof. trivial. Qed.
Lemma of_Z_1 {m} : of_Z m 1 = one.
Proof. apply to_Z_inj. rewrite to_Z_of_Z, to_Z_of_N; trivial. Qed.

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

Definition pow_N {m} (a : Zmod m) n := N.iter n (mul a) one.

Lemma pow_N_0_r {m} (x : Zmod m) : @pow_N m x 0 = one.
Proof. reflexivity. Qed.

Lemma pow_N_succ_r {m} (x : Zmod m) n : pow_N x (N.succ n) = mul x (pow_N x n).
Proof. cbv [pow_N]. rewrite N.iter_succ; trivial. Qed.

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
Module N.
  Lemma mod_pow_l a b c : ((a mod c)^b mod c = ((a ^ b) mod c))%N.
  Proof.
    induction b using N.peano_ind; intros; trivial; pose proof N.Div0.mul_mod.
    rewrite ?N.pow_succ_r', <-N.Div0.mul_mod_idemp_r, IHb; auto.
  Qed.
End N.

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

Lemma invmod_coprime a m (Hm : 1 < m) (H : Z.gcd a m = 1) : invmod a m * a mod m = 1.
Proof. rewrite invmod_coprime', Z.mod_1_l; lia. Qed.

Lemma invmod_prime a m (Hm : prime m) (H : a mod m <> 0) : invmod a m * a mod m = 1.
Proof.
  pose proof prime_ge_2 _ Hm as Hm'. rewrite Z.mod_divide in H by lia.
  apply invmod_coprime, Zgcd_1_rel_prime, rel_prime_sym, prime_rel_prime; auto; lia.
Qed.
End Znumtheory.

Definition inv {m} (x : Zmod m) : Zmod m := of_Z m (invmod (to_Z x) m).
Definition div {m} (x y : Zmod m) : Zmod m := of_Z m (invmod (to_Z y) m * x).

Module Import Notations.
  Declare Scope Zmod_scope.
  Delimit Scope Zmod_scope with Zmod.
  (* Bind Scope Zmod_scope with Zmod. *)
  Infix "*" := mul : Zmod_scope.
  Infix "+" := add : Zmod_scope.
  Infix "-" := sub : Zmod_scope.
  Infix "/" := div : Zmod_scope.
  Notation "- x" := (opp x) : Zmod_scope.
End Notations.

Lemma to_Z_inv {m} x : to_Z (@inv m x) = invmod x m mod m.
Proof. cbv [inv]. rewrite to_Z_of_Z. trivial. Qed.

Lemma to_N_one {m : positive} (Hm : 2 <= m) : @to_N m one = 1%N.
Proof. rewrite to_N_of_N, N.mod_small; lia. Qed.

Lemma to_Z_one {m : positive} (Hm : 2 <= m) : @to_Z m one = 1.
Proof. rewrite to_Z_of_N, Z.mod_small; lia. Qed.

Lemma one_neq_zero {m : positive} (Hm : 2 <= m) : one <> zero :> Zmod m.
Proof.
  intro H. apply (f_equal to_N) in H.
  rewrite to_N_one, to_N_0 in H; lia.
Qed.

Lemma to_N_nz {m} (x : Zmod m) (H : x <> zero) : to_N x <> 0%N.
Proof. intros X; apply H, to_N_inj. rewrite X; trivial. Qed.

Lemma to_Z_nz {m} (x : Zmod m) (H : x <> zero) : to_Z x <> 0.
Proof. intros X; apply H, to_Z_inj. rewrite X; trivial. Qed.

Lemma mul_inv_l {m} (x y : Zmod m) : mul (inv y) x = div x y.
Proof.
  apply to_Z_inj. cbv [div inv].
  rewrite to_Z_mul, !to_Z_of_Z, !Z.mul_mod_idemp_l; auto; inversion 1.
Qed.

Lemma mul_inv_r {m} (x y : Zmod m) : mul x (inv y) = div x y.
Proof. rewrite mul_comm, mul_inv_l; trivial. Qed.

Lemma div_same {m} (a : Zmod m) : div a a = of_Z m (Z.gcd a m).
Proof.
  rewrite <-mul_inv_l. apply to_Z_inj. rewrite to_Z_mul, to_Z_inv,
    Z.mul_mod_idemp_l, to_Z_of_Z, invmod_ok by inversion 1; trivial.
Qed.

Lemma div_same_coprime {m} (a : Zmod m) (H : Z.gcd a m = 1) : div a a = one.
Proof. rewrite div_same, H, of_Z_1; trivial. Qed.

Lemma div_same_prime {m} (x : Zmod m) (Hm : prime m) (H : x <> zero) : div x x = one.
Proof.
  apply to_Z_inj. apply to_Z_nz in H. pose proof to_Z_range x.
  rewrite <-mul_inv_l, to_Z_mul, to_Z_inv, Z.mul_mod_idemp_l, to_Z_one,
    invmod_prime; trivial; rewrite ?Z.mod_small; try lia.
Qed.

Lemma mul_inv_same_l_prime {m} (x : Zmod m) (Hm : prime m) (H : x <> zero) :
  mul (inv x) x = one.
Proof. intros; rewrite ?mul_inv_r, ?mul_inv_l, ?div_same_prime; trivial. Qed.

Lemma field_theory (m : positive) (Hm : prime m) :
  @Field_theory.field_theory (Zmod m) zero one add mul sub opp div inv eq.
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
  rewrite to_Z_one, Z.gcd_1_l; lia.
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

(** Alternative conversion function for mapping [Zmod m] to [-m/2, m/2) *)
Definition signed {m} (x : Zmod m) : Z :=
  if N.ltb (N.double x) m then x else x-m.

Lemma smod_unsigned {m} (x : Zmod m) : Z.smodulo (unsigned x) m = signed x.
Proof.
  pose proof to_Z_range x. cbv [signed unsigned Z.smodulo] in *.
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

(** Optimized conversions and operations for m=2^w *)
(* TODO: move to some ZArith rile *)
Module Pos.
Definition ones (p : positive) : positive :=
  N.iter (Pos.pred_N p) (fun n => n~1)%positive xH.
End Pos.
Module Import NN.
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
End NN.
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

(** Tests *)

Goal True. unify (add (of_N_value 4 3 I) (of_Z_pow2 2 1)) (of_Z 4 0). Abort.
Goal True. pose (((of_N_value 4 3 I) - (of_Z_pow2 2 1) + of_Z _ 2)). cbv in z. Abort.
Add Ring ring_Zmod2 : (@ring_theory 2).
Add Ring ring_Zmod2p1 : (@ring_theory (2^1)).
Goal True. assert (one - one = zero :> Zmod 2) as _ by ring. Abort.
Goal True. assert (of_Z _ 1 - of_Z _ 1 = zero :> Zmod (2^1)) as _ by ring. Abort.
