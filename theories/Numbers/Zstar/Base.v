Require Import Coq.Numbers.Zmod.TODO_MOVE. Import TODO_MOVE.Znumtheory.

Require Import Coq.NArith.NArith Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.ZArith.Znumtheory.

Require Import Coq.Numbers.Zmod.Base.

Require Import Coq.Bool.Bool.

Local Open Scope Z_scope.
Import Zmod.Base.Coercions.

Module Import Zmod. (* TODO: can we do better than this path hack? *)
  Include Zmod.Base.
End Zmod.

Record Zstar (m : positive) := of_N_value {
  to_N : N ; _ : Is_true ((to_N <? N.pos m) && (N.gcd to_N m =? 1))%N }.
Arguments to_N {m}.

Lemma to_N_inj {m} (x y : Zstar m) : to_N x = to_N y -> x = y.
Proof. cbv [to_N]; destruct x, y, 1. apply f_equal, Is_true_hprop. Qed.

Lemma to_N_range {m} (x : Zstar m) : (to_N x < m /\ N.gcd (to_N x) m = 1)%N.
Proof.
  case x as [x H]; cbn [to_N].
  eapply Is_true_eq_true, andb_true_iff in H.
  rewrite <-N.ltb_lt, <-N.eqb_eq; trivial.
Qed.

Definition to_Z {m} (x : Zstar m) := Z.of_N (to_N x).
Notation unsigned := to_Z (only parsing).

Lemma to_Z_inj {m} (x y : Zstar m) : to_Z x = to_Z y -> x = y.
Proof. auto using N2Z.inj, to_N_inj. Qed.

Lemma to_Z_range {m} (x : Zstar m) : to_Z x < m /\ Z.gcd (to_Z x) m = 1.
Proof.
  pose proof to_N_range x; cbv [to_Z].
  rewrite <-N2Z.inj_pos, Z.gcd_of_N; lia.
Qed.

Definition to_Zmod {m : positive} (a : Zstar m) : Zmod m.
  refine (Zmod.of_small_N m (to_N a) _).
  abstract (intros; apply to_N_range).
Defined.

Lemma to_N_to_Zmod {m} (x : Zstar m) : Zmod.to_N (to_Zmod x) = to_N x.
Proof. apply Zmod.to_N_of_small_N. Qed.

Lemma to_Z_to_Zmod {m} (x : Zstar m) : Zmod.to_Z (to_Zmod x) = to_Z x.
Proof.  apply Zmod.to_Z_of_small_N. Qed.

Lemma Ncoprime_to_Zmod {m} (x : Zstar m) : N.gcd (to_Zmod x) m = 1%N.
Proof. apply to_N_range. Qed.

Lemma coprime_to_Zmod {m} (x : Zstar m) : Z.gcd (to_Zmod x) m = 1.
Proof. rewrite to_Z_to_Zmod. apply to_Z_range. Qed.

Lemma to_Zmod_inj {m} (x y : Zstar m) : to_Zmod x = to_Zmod y -> x = y.
Proof.
  intros. apply to_N_inj.
  apply (f_equal Zmod.to_N) in H; rewrite 2 to_N_to_Zmod in H; trivial.
Qed.

Definition of_small_coprime_N m (n : N) (H : True -> (n < N.pos m)%N /\ N.gcd n m = 1%N) : Zstar m.
  refine (of_N_value m n (transparent_true _ (fun _ => _))).
  abstract (apply Is_true_eq_left, andb_true_intro, conj; [apply N.ltb_lt|apply N.eqb_eq]; apply H, I).
Defined.

Lemma to_N_of_small_coprime_N {m} n pf : to_N (of_small_coprime_N m n pf) = n. Proof. trivial. Qed.

Lemma to_Z_of_small_coprime_N {m} n pf : to_Z (of_small_coprime_N m n pf) = n. Proof. trivial. Qed.

Definition of_coprime_N (m : positive) (z : N) (H : True -> N.gcd z m = 1%N) : Zstar m.
  refine (of_small_coprime_N m (z mod m) (fun _ => _)).
  abstract (rewrite N.Lcm0.gcd_mod, N.gcd_comm; zify; Z.to_euclidean_division_equations; try lia).
Defined.

Lemma to_N_of_coprime_N {m} n pf : to_N (of_coprime_N m n pf) = N.modulo n m. Proof. trivial. Qed.

Definition of_small_coprime_Z m (z : Z) (H : True -> (0 <= z < Z.pos m)%Z /\ Z.gcd z m = 1%Z) : Zstar m.
  refine (of_small_coprime_N m (Z.to_N z) (fun _ => _)).
  abstract ( split; [|apply N2Z.inj; rewrite <-Z.gcd_of_N, !N2Z.inj_pos, !Z2N.id]; lia).
Defined.

Lemma to_N_of_small_coprime_Z {m} n pf : to_N (of_small_coprime_Z m n pf) = Z.to_N n.
Proof. apply to_N_of_small_coprime_N. Qed.

Lemma to_Z_of_small_coprime_Z {m} n pf : to_Z (of_small_coprime_Z m n pf) = n.
Proof. cbv [to_Z]. rewrite to_N_of_small_coprime_Z; lia. Qed.

Definition of_coprime_Z (m : positive) (z : Z) (H : True -> Z.gcd z m = 1%Z) : Zstar m.
  refine (of_small_coprime_Z m (z mod m) (fun _ => _)).
  abstract (rewrite Z.gcd_mod, Z.gcd_comm; Z.div_mod_to_equations; try lia).
Defined.

Lemma to_N_of_coprime_Z {m} n pf : to_N (of_coprime_Z m n pf) = Z.to_N (n mod m).
Proof. apply to_N_of_small_coprime_Z. Qed.

Lemma to_Z_of_coprime_Z {m} n pf : to_Z (of_coprime_Z m n pf) = n mod m.
Proof. apply to_Z_of_small_coprime_Z. Qed.

Definition of_coprime_Zmod {m} (x : Zmod m) (H : True -> Z.gcd x m = 1%Z) : Zstar m.
  refine (of_small_coprime_Z m x (fun _ => _)).
  abstract auto using Zmod.to_Z_range.
Defined.

Lemma to_Z_of_coprime_Zmod {m} x pf : to_Z (@of_coprime_Zmod m x pf) = x.
Proof. apply to_Z_of_small_coprime_Z. Qed.

Lemma to_Zmod_of_coprime_Zmod {m} x pf : to_Zmod (@of_coprime_Zmod m x pf) = x.
Proof. apply Zmod.to_Z_inj. rewrite to_Z_to_Zmod. apply to_Z_of_coprime_Zmod. Qed.

Lemma hprop_Zstar_1 (a b : Zstar 1) : a = b.
Proof.
  pose proof to_N_range a; pose proof to_N_range b; apply to_N_inj; lia.
Qed.

Lemma wlog_eq_Zmod_2 {m} (a b : Zstar m) (k : 2 <= m -> a = b) : a = b.
Proof.
  destruct (Pos.eq_dec 1 m) as [e|ne].
  { destruct e; auto using hprop_Zstar_1. }
  { apply k; lia. }
Qed.

Module Import Coercions.
  Coercion to_Z : Zstar >-> Z.
  Coercion to_N : Zstar >-> N.
  Coercion to_Zmod : Zstar >-> Zmod.
End Coercions.

Definition of_Zmod_option {m} (x : Zmod m) : option (Zstar m).
  refine (if N.eq_dec (N.gcd x m) 1 then Some (of_small_coprime_N m x (fun _ => _)) else None).
  abstract auto using Zmod.to_N_range, e.
Defined.

Lemma of_Zmod_option_to_Zmod {m} (x : Zstar m) : of_Zmod_option x = Some x.
Proof.
  cbv [of_Zmod_option].
  case N.eq_dec as [].
  { apply f_equal, to_N_inj; rewrite to_N_of_small_coprime_N, to_N_to_Zmod; trivial. }
  { pose proof to_N_range x. rewrite to_N_to_Zmod in n; intuition idtac. }
Qed.

Lemma of_Zmod_option_Some {m} x y : @of_Zmod_option m x = Some y -> x = to_Zmod y.
Proof.
  cbv [of_Zmod_option].
  case N.eq_dec as []; inversion 1; subst.
  apply Zmod.to_N_inj. rewrite to_N_to_Zmod; trivial.
Qed.

Lemma of_Zmod_option_None {m} (x : Zmod m) : @of_Zmod_option m x = None <-> N.gcd x m <> 1%N.
Proof.
  cbv [of_Zmod_option]; case N.eq_dec as []; intuition congruence.
Qed.

Lemma of_Zmod_option_None_prime {m} (x : Zmod m) (Hm : prime m)
  (Hx : @of_Zmod_option m x = None) : x = Zmod.zero.
Proof.
  apply Zmod.to_Z_inj.
  case (Z.eqb_spec (Zmod.to_Z x) (@Zmod.to_Z m Zmod.zero)); trivial; intros; exfalso; cbn in *.
  eapply of_Zmod_option_None in Hx; eapply Hx; clear Hx.
  pose proof Zmod.to_Z_range x.
  rewrite <-N2Z.inj_iff, <-Z.gcd_of_N, Zgcd_1_rel_prime.
  progress change (Z.of_N (Zmod.to_N x)) with (Zmod.to_Z x).
  apply rel_prime_sym, prime_rel_prime; trivial.
  intros ?%Z.divide_pos_le; try lia.
Qed.

Definition elements m : list (Zstar m) := List.mapfilter of_Zmod_option (Zmod.elements m).

Lemma in_elements m (x : Zstar m) : List.In x (elements m).
Proof.
  apply List.in_mapfilter.
  exists (to_Zmod x).
  split; trivial using Zmod.in_elements, of_Zmod_option_to_Zmod.
Qed.

Lemma NoDup_elements {m} : List.NoDup (elements m).
Proof.
  eapply List.NoDup_mapfilter, Zmod.NoDup_elements.
  intros * H HX.
  case of_Zmod_option eqn:G; trivial; contradict HX; symmetry in H.
  apply of_Zmod_option_Some in G, H; congruence.
Qed.

(** Multiplication *)

Definition one {m} : Zstar m.
  refine (of_small_coprime_N m (if Pos.eqb m 1 then 0 else 1) _).
  abstract (destruct (Pos.eqb_spec m 1) as [->|?]; rewrite ?N.gcd_0_l, ?N.gcd_1_l; lia).
Defined.

Lemma to_N_1 {m : positive} : 2 <= m -> @to_N m one = 1%N.
Proof. cbv [one]. rewrite to_N_of_small_coprime_N. destruct (Pos.eqb_spec m 1); lia. Qed.

Lemma to_Z_1 {m : positive} : 2 <= m -> @to_Z m one = 1%Z.
Proof. cbv [one]. rewrite to_Z_of_small_coprime_N. destruct (Pos.eqb_spec m 1); lia. Qed.

Lemma to_Zmod_1 {m} : @to_Zmod m one = Zmod.one.
Proof.
  apply Zmod.to_N_inj. rewrite to_N_to_Zmod. cbv [to_N Zmod.to_N one Zmod.one].
  destruct (Pos.eqb_spec m 1) as [->|?]; cbn; trivial; case m; trivial.
Qed.

Definition mul {m} (a b : Zstar m) : Zstar m.
  refine (of_small_coprime_N m (a * b mod m) _)%positive.
  abstract (split;
    [ apply N.mod_upper_bound; inversion 1
    | rewrite N.Lcm0.gcd_mod, N.gcd_comm; apply N.coprime_mul; apply to_N_range ]).
Defined.

Lemma to_N_mul {m} (a b : Zstar m) : @to_N m (mul a b) = (a * b mod m)%N.
Proof. apply to_N_of_small_coprime_N. Qed.

Lemma to_Z_mul {m} (a b : Zstar m) : @to_Z m (mul a b) = a * b mod m.
Proof. cbv [mul]; rewrite to_Z_of_small_coprime_N, N2Z.inj_mod, N2Z.inj_mul; trivial. Qed.

Lemma to_Zmod_mul {m} (a b : Zstar m) : @to_Zmod m (mul a b) = Zmod.mul a b.
Proof.
  apply Zmod.to_N_inj. repeat rewrite ?to_N_mul, ?to_N_to_Zmod, ?Zmod.to_N_mul; trivial.
Qed.

Lemma mul_assoc {m} a b c : @mul m a (mul b c) = mul (mul a b) c.
Proof. apply to_Zmod_inj; rewrite ?to_Zmod_mul; apply Zmod.mul_assoc. Qed.
Lemma mul_comm {m} a b : @mul m a b = mul b a.
Proof. apply to_Zmod_inj; rewrite ?to_Zmod_mul; apply Zmod.mul_comm. Qed.
Lemma mul_1_l {m} a : @mul m one a = a. Proof.
Proof. apply to_Zmod_inj; rewrite ?to_Zmod_mul, to_Zmod_1. apply Zmod.mul_1_l. Qed.
Lemma mul_1_r {m} a : @mul m a one = a. Proof. rewrite <-mul_comm; apply mul_1_l. Qed.

(** Inverse and divition *)

Definition inv {m} (x : Zstar m) : Zstar m.
  refine (of_coprime_Z m (Znumtheory.invmod (to_Z x) m) (fun _ => _)).
  abstract (apply Znumtheory.coprime_invmod, to_Z_range).
Defined.

Lemma to_Z_inv {m} x : to_Z (@inv m x) = invmod x m mod m.
Proof. apply to_Z_of_coprime_Z. Qed.

Lemma to_Zmod_inv {m} x : to_Zmod (@inv m x) = Zmod.inv x.
Proof. apply Zmod.to_Z_inj. rewrite to_Z_to_Zmod, to_Z_inv, Zmod.to_Z_inv; trivial. Qed.

Definition div {m} (x y : Zstar m) : Zstar m := mul x (inv y).

Lemma to_Z_div {m} x y : to_Z (@div m x y) = x * invmod y m mod m.
Proof. cbv [div]. rewrite to_Z_mul, to_Z_inv, Zmult_mod_idemp_r; trivial. Qed.

Lemma mul_inv_l {m} x y : mul (@inv m y) x = div x y.
Proof. apply to_Z_inj. cbv [div inv]. rewrite mul_comm; trivial. Qed.

Lemma mul_inv_r {m} x y : mul x (@inv m y) = div x y.
Proof. rewrite mul_comm, mul_inv_l; trivial. Qed.

Lemma div_same {m} (a : Zstar m) : div a a = one.
Proof.
  apply wlog_eq_Zmod_2; intros; apply to_Z_inj.
  rewrite to_Z_div, Z.mul_comm, invmod_coprime, to_Z_1; trivial. apply to_Z_range.
Qed.

Lemma mul_inv_same_l {m} x : mul (@inv m x) x = one.
Proof. apply wlog_eq_Zmod_2; rewrite mul_inv_l, div_same; trivial; apply to_Z_range. Qed.

Lemma mul_inv_same_r {m} x : mul x (@inv m x) = one.
Proof. rewrite mul_comm; apply mul_inv_same_l. Qed.

Lemma inv_inv {m} x : inv (@inv m x) = x.
Proof.
  rewrite <-mul_1_r, <-(mul_inv_same_l (inv x)), (mul_comm _ (inv x)); auto.
  rewrite mul_assoc, (mul_comm x), (mul_inv_same_l x), mul_1_l; auto.
Qed.

Lemma inv_1 {m} : @inv m one = one.
Proof.
  apply wlog_eq_Zmod_2; intros.
  symmetry; rewrite <-mul_1_l, mul_inv_r, div_same; trivial.
Qed.

Lemma mul_cancel_l {m} (a b c : Zstar m) (H : mul a b = mul a c) : b = c.
Proof.
  apply wlog_eq_Zmod_2; intros. apply (f_equal (fun x => mul (inv a) x)) in H.
  rewrite !mul_assoc, !mul_inv_same_l, !mul_1_l in H; trivial.
Qed.

Lemma mul_cancel_r {m} (a b c : Zstar m) (H : mul b a = mul c a) : b = c.
Proof. rewrite 2(mul_comm _ a) in H; apply mul_cancel_l in H; trivial. Qed.

Lemma to_Zmod_elements_prime (m : positive) (H : prime m) :
  List.map to_Zmod (elements m) = List.tl (Zmod.elements m).
Proof.
  cbv [elements Zmod.elements]; rewrite List.tl_map.
  replace (Pos.to_nat m) with (S (Pos.to_nat m-1)) by lia;
    progress cbn [List.seq List.tl List.map List.mapfilter].
  rewrite (proj2 (of_Zmod_option_None _)); cycle 1.
  { rewrite @Zmod.to_N_0, N.gcd_0_l; pose proof prime_ge_2 m H; lia. }
  erewrite List.mapfilter_map, List.map_mapfilter, List.mapfilter_ext, List.mapfilter_Some; trivial.
  apply List.Forall_forall; intros i ?%List.in_seq.
  destruct of_Zmod_option eqn:Hx.
  { eapply of_Zmod_option_Some in Hx; rewrite Hx; trivial. } exfalso.
  eapply of_Zmod_option_None_prime in Hx; trivial.
  eapply (f_equal Zmod.to_Z) in Hx; progress cbn in Hx.
  rewrite Zmod.to_Z_of_nat, Z.mod_small in Hx; lia.
Qed.

Lemma length_elements_prime (m : positive) (H : prime m) : length (elements m) = N.to_nat (Pos.pred_N m).
Proof.
  erewrite <-List.map_length, to_Zmod_elements_prime, List.tl_length, Zmod.length_elements;
    trivial; lia.
Qed.

(** Non-negative powers *)

Definition pow_N {m} (a : Zstar m) n := N.iter_op mul one a n.

Lemma pow_N_correct {m} a n
  : @pow_N m a n = N.iter n (mul a) one.
Proof. apply N.iter_op_correct; auto using mul_1_r, mul_assoc. Qed.

Lemma pow_N_0_r {m} (x : Zstar m) : @pow_N m x 0 = one.
Proof. rewrite pow_N_correct; reflexivity. Qed.

Lemma pow_N_succ_r {m} (x : Zstar m) n : pow_N x (N.succ n) = mul x (pow_N x n).
Proof. rewrite !pow_N_correct, N.iter_succ; trivial. Qed.

Lemma to_Zmod_pow_N {m} (a : Zstar m) n : @to_Zmod m (pow_N a n) = Zmod.pow_N a n.
Proof.
  induction n using N.peano_ind; repeat rewrite
    ?pow_N_0_r, ?Zmod.pow_N_0_r, ?pow_N_succ_r, ?Zmod.pow_N_succ_r,
    ?IHn, ?to_Zmod_1, ?to_Zmod_mul; trivial.
Qed.

Lemma pow_N_1_l {m} n : @pow_N m one n = one.
Proof. apply to_Zmod_inj. rewrite to_Zmod_pow_N, to_Zmod_1, Zmod.pow_N_1_l; trivial. Qed.

Lemma to_N_pow_N {m} x n : @to_N m (pow_N x n) = (to_N x ^ n mod m)%N.
Proof. rewrite <-to_N_to_Zmod, to_Zmod_pow_N, Zmod.to_N_pow_N; trivial. Qed.

(** Integer powers *)

Definition pow_Z {m} (a : Zstar m) z :=
  if Z.ltb z 0 then inv (pow_N a (Z.abs_N z)) else pow_N a (Z.abs_N z).

Lemma pow_Z_0_r {m} x : @pow_Z m x 0 = one.
Proof. reflexivity. Qed.

Lemma pow_Z_1_l {m} z : @pow_Z m one z = one.
Proof.
  cbv [pow_Z]; case (Z.ltb_spec z 0) as [];
    rewrite ?pow_N_1_l, ?inv_1; trivial.
Qed.

Lemma pow_Z_N_r {m} a (n : N) : @pow_Z m a n = pow_N a n.
Proof. case n; trivial. Qed.

Lemma to_Z_pow_Z_nonneg {m} x z (Hz : 0 <= z) : @to_Z m (pow_Z x z) = x^z mod m.
Proof.
  cbv [pow_Z to_Z]; case (Z.ltb_spec z 0) as []; try lia.
  rewrite to_N_pow_N, N2Z.inj_mod, N2Z.inj_pow; f_equal; f_equal; lia.
Qed.

Lemma pow_Z_opp_r {m} a (z : Z) : @pow_Z m a (-z) = inv (pow_Z a z).
Proof.
  cbv [pow_Z]; case (Z.ltb_spec (-z) 0), (Z.ltb_spec z 0);
    try (replace z with 0%Z by lia); cbn;
    rewrite ?inv_inv, ?inv_1, ?Zabs2N.inj_opp; trivial.
Qed.

Lemma to_Z_pow_Z_neg {m} x z (Hz : z <= 0) :
  @to_Z m (pow_Z x z) = invmod (to_Z x^(-z)) m mod m.
Proof.
  replace z with (--z) at 1 by lia; rewrite pow_Z_opp_r by trivial.
  pose proof to_Z_range (pow_Z x (-z)); rewrite to_Z_inv, to_Z_pow_Z_nonneg in * by lia.
  rewrite invmod_mod_l; try lia.
  rewrite ?Z.gcd_mod, ?(Z.gcd_comm m) in *; trivial; subst; try lia.
Qed.
