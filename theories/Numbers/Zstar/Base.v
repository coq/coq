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

Definition of_small_coprime_N m (n : N) (H : True -> (n < N.pos m)%N /\ N.gcd n m = 1%N) : Zstar m.
  refine (of_N_value m n (transparent_true _ (fun _ => _))).
  abstract (apply Is_true_eq_left, andb_true_intro, conj; [apply N.ltb_lt|apply N.eqb_eq]; apply H, I).
Defined.

Definition one {m} : Zstar m.
  refine (of_small_coprime_N m (if Pos.eqb m 1 then 0 else 1) _).
  abstract (destruct (Pos.eqb_spec m 1) as [->|?]; rewrite ?N.gcd_0_l, ?N.gcd_1_l; lia).
Defined.

Module Import Private_to_N.

Lemma to_N_inj {m} (x y : Zstar m) : to_N x = to_N y -> x = y.
Proof. cbv [to_N]; destruct x, y, 1. apply f_equal, Is_true_hprop. Qed.

Lemma to_N_inj_iff {m} (x y : Zstar m) : to_N x = to_N y <-> x = y.
Proof. split; auto using to_N_inj; congruence. Qed.

Lemma to_N_range {m} (x : Zstar m) : (to_N x < m /\ N.gcd (to_N x) m = 1)%N.
Proof.
  case x as [x H]; cbn [to_N].
  eapply Is_true_eq_true, andb_true_iff in H.
  rewrite <-N.ltb_lt, <-N.eqb_eq; trivial.
Qed.

(* Note: there doesn't seem to be a natural cast from Zmod to Zstar. *)
(* Z.gcd_0_l : forall n : Z, Z.gcd 0 n = Z.abs n *)
(* Compute
  let x := 2^2*5 in (* 20 *)
  let m := 2*3^3 in  (* 54 *)
  let g := Z.gcd x m in (* 2 *)
  let y := Z.div x g in (* 10 *)
  let d := Z.gcd y m in (* 2 *)
  (m, g, y, d). *)
(* Could factor m and remove common factors from x, but that's slow *)
Definition of_Zmod {m} (x : Zmod m) : Zstar m.
  refine (if N.eq_dec (N.gcd x m) 1 then of_small_coprime_N m x (fun _ => _) else one).
  abstract auto using Zmod.to_N_range.
Defined.

Lemma to_N_of_small_coprime_N {m} n pf : to_N (of_small_coprime_N m n pf) = n. Proof. trivial. Qed.

Lemma to_N_of_Zmod' {m} (x : Zmod m) : 
  to_N (of_Zmod x) = if N.eqb (N.gcd x m) 1 then x else @to_N m one.
Proof. cbv [of_Zmod]. case (N.eqb_spec (N.gcd x m) 1), N.eq_dec; try lia; trivial. Qed.

Lemma to_N_of_Zmod {m} (x : Zmod m) (H : Z.gcd x m = 1) : to_N (of_Zmod x) = x.
Proof.
  rewrite to_N_of_Zmod'; case (N.eqb_spec (N.gcd x m) 1);
  rewrite <-?N2Z.inj_iff, <-?Z.gcd_of_N,  ?fold_to_Z in *; cbn; lia.
Qed.

Lemma to_N_1 {m : positive} : 2 <= m -> @to_N m one = 1%N.
Proof. cbv [one]. rewrite to_N_of_small_coprime_N. destruct (Pos.eqb_spec m 1); lia. Qed.

End Private_to_N.

Definition to_Zmod {m : positive} (a : Zstar m) : Zmod m.
  refine (Zmod.of_small_N m (to_N a) _).
  abstract (intros; apply to_N_range).
Defined.

Notation of_Zmod := of_Zmod.

Lemma to_N_to_Zmod {m : positive} (a : Zstar m) : Zmod.to_N (to_Zmod a) = to_N a.
Proof. trivial. Qed.

Lemma to_Zmod_1 {m} : @to_Zmod m one = Zmod.one.
Proof.
  apply Zmod.to_N_inj. rewrite to_N_to_Zmod. cbv [to_N Zmod.to_N one Zmod.one].
  destruct (Pos.eqb_spec m 1) as [->|?]; cbn; trivial; case m; trivial.
Qed.

Lemma Ncoprime_to_Zmod {m} (x : Zstar m) : N.gcd (to_Zmod x) m = 1%N.
Proof. apply to_N_range. Qed.

Lemma coprime_to_Zmod {m} (x : Zstar m) : Z.gcd (to_Zmod x) m = 1.
Proof.
  pose proof Ncoprime_to_Zmod x.
  rewrite <-fold_to_Z, <-N2Z.inj_pos, Z.gcd_of_N; lia.
Qed.
Notation to_Zmod_range := coprime_to_Zmod.

Lemma to_Zmod_inj {m} (x y : Zstar m) : to_Zmod x = to_Zmod y -> x = y.
Proof. intros ?%(f_equal Zmod.to_N); rewrite 2to_N_to_Zmod in *; auto using to_N_inj. Qed.

Lemma to_Zmod_inj_iff {m} (x y : Zstar m) : to_Zmod x = to_Zmod y <-> x = y.
Proof. split; auto using to_Zmod_inj; congruence. Qed.

Lemma of_Zmod_to_Zmod {m} x : @of_Zmod m (to_Zmod x) = x.
Proof.
  pose proof to_Zmod_range x. apply to_N_inj.
  cbv [of_Zmod]; destruct N.eq_dec; auto using to_N_of_small_coprime_N.
  rewrite <-Zmod.fold_to_Z, <-N2Z.inj_pos, Z.gcd_of_N in *; lia.
Qed.

Lemma to_Zmod_of_Zmod {m} (x : Zmod m) : Z.gcd x m = 1 -> to_Zmod (of_Zmod x) = x.
Proof. intro; apply Zmod.to_N_inj. rewrite to_N_to_Zmod, to_N_of_Zmod; trivial. Qed.

Module Private_to_Z.
Definition to_Z {m} (x : Zstar m) := Z.of_N (to_N x).
Notation unsigned := to_Z (only parsing).

Lemma to_Z_inj {m} (x y : Zstar m) : to_Z x = to_Z y -> x = y.
Proof. auto using N2Z.inj, to_N_inj. Qed.

Lemma to_Z_range {m} (x : Zstar m) : 0 <= to_Z x < m /\ Z.gcd (to_Z x) m = 1.
Proof.
  pose proof to_N_range x; cbv [to_Z].
  rewrite <-N2Z.inj_pos, Z.gcd_of_N; lia.
Qed.

Lemma to_Z_to_Zmod {m} (x : Zstar m) : Zmod.to_Z (to_Zmod x) = to_Z x.
Proof.  apply Zmod.to_Z_of_small_N. Qed.

Lemma to_Z_of_small_coprime_N {m} n pf : to_Z (of_small_coprime_N m n pf) = n. Proof. trivial. Qed.

Lemma to_Z_1 {m : positive} : 2 <= m -> @to_Z m one = 1%Z.
Proof. cbv [one]. rewrite to_Z_of_small_coprime_N. destruct (Pos.eqb_spec m 1); lia. Qed.
End Private_to_Z.

Module Private_of_N_Z. Import Private_to_Z.
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
End Private_of_N_Z.

Module Import Coercions.
  Coercion to_Zmod : Zstar >-> Zmod.
End Coercions.

Lemma hprop_Zstar_1 (a b : Zstar 1) : a = b.
Proof.
  pose proof to_N_range a; pose proof to_N_range b; apply to_N_inj; lia.
Qed.

Lemma hprop_Zstar_2 (a b : Zstar 2) : a = b.
Proof.
  pose proof to_Zmod_range a; pose proof to_Zmod_range b.
  pose proof Zmod.to_Z_range a; pose proof Zmod.to_Z_range b.
  apply to_Zmod_inj, Zmod.to_Z_inj;
  assert (to_Z a = 0 \/ to_Z a = 1) as [Ha|Ha] by lia;
  assert (to_Z b = 0 \/ to_Z b = 1) as [Hb|Hb] by lia;
  rewrite ?Ha, ?Hb in *; cbn in *; intuition try lia.
Qed.

Lemma wlog_eq_Zstar_3 {m} (a b : Zstar m) (k : 3 <= m -> a = b) : a = b.
Proof.
  destruct (Pos.eq_dec 1 m) as [e|].
  { destruct e; auto using hprop_Zstar_1. }
  destruct (Pos.eq_dec 2 m) as [e'|].
  { destruct e'; auto using hprop_Zstar_2. }
  { apply k; lia. }
Qed.

Definition elements m : list (Zstar m) :=
  List.map of_Zmod (List.filter (fun x : Zmod _ => Z.eqb (Z.gcd x m) 1) (Zmod.elements m)).

Lemma in_elements m (x : Zstar m) : List.In x (elements m).
Proof.
  eapply List.in_map_iff, (ex_intro _ (to_Zmod x)), conj, List.filter_In, conj,
    Z.eqb_eq; eauto using of_Zmod_to_Zmod, Zmod.in_elements, to_Zmod_range.
Qed.

Lemma NoDup_elements {m} : List.NoDup (elements m).
Proof.
  (* List.NoDup_map_iff *)
  eapply FinFun.Injective_map_NoDup, List.NoDup_filter, NoDup_elements.
Admitted.

(** Multiplication *)

Definition mul {m} (a b : Zstar m) : Zstar m.
  refine (of_small_coprime_N m (a * b mod m) _)%positive.
  abstract (split;
    [ apply N.mod_upper_bound; inversion 1
    | rewrite N.Lcm0.gcd_mod, N.gcd_comm; apply N.coprime_mul; apply to_N_range ]).
Defined.

Lemma to_Zmod_mul {m} (a b : Zstar m) : @to_Zmod m (mul a b) = Zmod.mul a b.
Proof.
  apply Zmod.to_N_inj. repeat rewrite ?to_N_mul, ?to_N_to_Zmod, ?Zmod.to_N_mul; trivial.
Qed.

Module Private_mul.
Lemma to_N_mul {m} (a b : Zstar m) : @to_N m (mul a b) = (a * b mod m)%N.
Proof. apply to_N_of_small_coprime_N. Qed.

(*
Lemma to_Z_mul {m} (a b : Zstar m) : @Zstar.to_Z m (mul a b) = a * b mod m.
Proof. cbv [mul]; rewrite to_Z_of_small_coprime_N, N2Z.inj_mod, N2Z.inj_mul; trivial. Qed.
*)
End Private_mul.

Lemma mul_assoc {m} a b c : @mul m a (mul b c) = mul (mul a b) c.
Proof. apply to_Zmod_inj; rewrite ?to_Zmod_mul; apply Zmod.mul_assoc. Qed.
Lemma mul_comm {m} a b : @mul m a b = mul b a.
Proof. apply to_Zmod_inj; rewrite ?to_Zmod_mul; apply Zmod.mul_comm. Qed.
Lemma mul_1_l {m} a : @mul m one a = a. Proof.
Proof. apply to_Zmod_inj; rewrite ?to_Zmod_mul, to_Zmod_1. apply Zmod.mul_1_l. Qed.
Lemma mul_1_r {m} a : @mul m a one = a. Proof. rewrite <-mul_comm; apply mul_1_l. Qed.

(** Inverse and divition *)

Definition inv {m} (x : Zstar m) : Zstar m := of_Zmod (Zmod.inv x).

Lemma to_Zmod_inv {m} x : to_Zmod (@inv m x) = Zmod.inv x.
Proof. 
  cbv [inv]. rewrite to_Zmod_of_Zmod; trivial.
  rewrite to_Z_inv, Z.gcd_mod, Z.gcd_comm;
    auto using coprime_invmod, to_Zmod_range; lia.
Qed.

Definition div {m} (x y : Zstar m) : Zstar m := mul x (inv y).

Lemma to_Zmod_div {m} x y : to_Zmod (@div m x y) = Zmod.ndiv x y.
Proof. cbv [div ndiv]. rewrite to_Zmod_mul, to_Zmod_inv; trivial. Qed.

(*
Lemma to_Z_div {m} x y : to_Z (@div m x y) = x * invmod y m mod m.
Proof. rewrite to_Zmod_div, to_Z_ndiv; trivial. Qed.
*)

Lemma mul_inv_r {m} x y : mul x (@inv m y) = div x y.
Proof. apply to_Zmod_inj. trivial. Qed.

Lemma mul_inv_l {m} x y : mul (@inv m y) x = div x y.
Proof. rewrite mul_comm, mul_inv_r; trivial. Qed.

Lemma div_same {m} (a : Zstar m) : div a a = one.
Proof.
  pose proof to_Zmod_range a; apply wlog_eq_Zstar_3; intros.
  apply to_Zmod_inj, to_Z_inj.
  rewrite to_Zmod_div, Base.to_Z_ndiv, Z.mul_comm, invmod_coprime, to_Zmod_1, to_Z_1; try lia.
Qed.

Lemma mul_inv_same_l {m} x : mul (@inv m x) x = one.
Proof. apply wlog_eq_Zstar_3; rewrite mul_inv_l, div_same; trivial; apply to_Z_range. Qed.

Lemma mul_inv_same_r {m} x : mul x (@inv m x) = one.
Proof. rewrite mul_comm; apply mul_inv_same_l. Qed.

Lemma inv_inv {m} x : inv (@inv m x) = x.
Proof.
  rewrite <-mul_1_r, <-(mul_inv_same_l (inv x)), (mul_comm _ (inv x)); auto.
  rewrite mul_assoc, (mul_comm x), (mul_inv_same_l x), mul_1_l; auto.
Qed.

Lemma inv_1 {m} : @inv m one = one.
Proof.
  apply wlog_eq_Zstar_3; intros.
  symmetry; rewrite <-mul_1_l, mul_inv_r, div_same; trivial.
Qed.

Lemma mul_cancel_l {m} (a b c : Zstar m) (H : mul a b = mul a c) : b = c.
Proof.
  apply wlog_eq_Zstar_3; intros. apply (f_equal (fun x => mul (inv a) x)) in H.
  rewrite !mul_assoc, !mul_inv_same_l, !mul_1_l in H; trivial.
Qed.

Lemma mul_cancel_r {m} (a b c : Zstar m) (H : mul b a = mul c a) : b = c.
Proof. rewrite 2(mul_comm _ a) in H; apply mul_cancel_l in H; trivial. Qed.

Lemma to_Zmod_elements_prime (m : positive) (H : prime m) :
  List.map to_Zmod (elements m) = List.tl (Zmod.elements m).
Proof.
  cbv [elements Zmod.elements]; rewrite List.tl_map.
  erewrite List.map_map, List.map_ext_in, List.map_id; cycle 1.
  { intros ? [? ?%Z.eqb_eq]%List.filter_In. auto using to_Zmod_of_Zmod. }
  replace (Pos.to_nat m) with (S (Pos.to_nat m-1)) by lia;
    progress cbn [List.seq List.tl List.map List.filter].
  rewrite to_Z_of_nat; progress simpl Z.gcd; destruct (Z.eqb_spec m 1);
    [pose proof prime_ge_2 m H; lia|].
  apply List.forallb_filter_id, List.forallb_forall.
  intros ? (i&?&?%List.in_seq)%List.in_map_iff; subst.
  apply Z.eqb_eq, Zgcd_1_rel_prime, rel_prime_le_prime; trivial.
  rewrite to_Z_of_nat, Z.mod_small; lia.
Qed.

Lemma TODO_positive_elements_coprime {a b} : exists l, elements (a*b) = l.
Proof.
  eexists.
  cbv [elements Zmod.elements].
  rewrite Pos2Nat.inj_mul, List.seq_mul_r.
  rewrite List.flat_map_concat_map, List.concat_map, List.map_map, <-List.flat_map_concat_map; cbn [Nat.add].
  rewrite List.filter_flat_map.
  erewrite List.flat_map_ext; cycle -1. { intros k.
  erewrite List.map_ext_in; cycle -1. {
  intros i ?%List.in_seq.
Abort.

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
  rewrite to_Zmod_pow_N, Zmod.to_N_pow_N.
  rewrite N2Z.inj_mod, N2Z.inj_pow; f_equal; f_equal; lia.
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
  pose proof to_Zmod_range (pow_Z x (-z)).
  rewrite to_Zmod_inv, to_Z_inv, to_Z_pow_Z_nonneg in * by lia.
  rewrite invmod_mod_l; try lia.
  rewrite ?Z.gcd_mod, ?(Z.gcd_comm m) in *; trivial; subst; try lia.
Qed.
