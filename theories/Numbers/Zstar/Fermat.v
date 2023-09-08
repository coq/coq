(* TODO: move out of Zstar *)

Require Import Coq.Numbers.Zmod.TODO_MOVE.

Require Import Coq.NArith.NArith Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Numbers.Zmod.Base Coq.Numbers.Zmod.Inverse Coq.Numbers.Zstar.Base.
Require Coq.Sorting.Permutation.
Local Notation Permutation := Permutation.Permutation.

Local Open Scope Z_scope.

Import Zmod.Base.Coercions.
Import Zstar.Base.Coercions.

Module Zstar.
Lemma prod_Permutation {m} one (xs ys : list (Zstar m)) (H : Permutation xs ys) :
  List.fold_right mul one xs = List.fold_right mul one ys.
Proof. induction H; cbn; repeat rewrite ?mul_assoc, ?(mul_comm x); congruence. Qed.

Lemma prod_repeat {m} (a : Zstar m) n :
  List.fold_right mul one (List.repeat a n) = pow_N a (N.of_nat n).
Proof.
  induction n as [|n]; cbn [List.fold_right List.repeat];
    rewrite ?pow_N_0_r, ?mul_1_r, ?Nat2N.inj_succ, ?pow_N_succ_r, ?IHn; trivial.
Qed.

Lemma prod_map_mul {m} (a : Zstar m) xs :
  List.fold_right mul one (List.map (mul a) xs) =
  mul (pow_N a (N.of_nat (length xs))) (List.fold_right mul one xs).
Proof.
  induction xs as [|x xs]; cbn [List.fold_right List.map length];
    rewrite ?pow_N_0_r, ?mul_1_r, ?Nat2N.inj_succ, ?pow_N_succ_r, ?IHxs; trivial.
  repeat rewrite ?mul_assoc, ?(mul_comm _ x); trivial.
Qed.

Local Hint Unfold FinFun.Injective List.incl : core.
Lemma Permutation_mul_elements {m} (a : Zstar m) :
  Permutation (List.map (mul a) (elements m)) (elements m).
Proof.
  eauto 6 using Permutation.Permutation_map_same_l, FinFun.Injective_map_NoDup, NoDup_elements, mul_cancel_l, in_elements.
Qed.

Theorem euler {m} (a : Zstar m) : pow_N a (N.of_nat (length (elements m))) = one.
Proof.
  epose proof prod_map_mul a (elements m) as P.
  erewrite prod_Permutation in P by eapply Permutation_mul_elements.
  rewrite <-mul_1_l in P at 1. eapply mul_cancel_r, eq_sym in P; trivial.
Qed.

Theorem fermat {m} (a : Zstar m) (H : prime m) : pow_N a (Pos.pred_N m) = one.
Proof. erewrite <-euler, Zstar.length_elements_prime; trivial; f_equal; lia. Qed.

Theorem fermat_inv {m} (a : Zstar m) (H : prime m) :
  Zstar.pow_N a (N.pred (Pos.pred_N m)) = Zstar.inv a.
Proof.
  eapply mul_cancel_l; try eassumption.
  rewrite <-Zstar.pow_N_succ_r, N.succ_pred, fermat, mul_inv_same_r;
    trivial; pose proof prime_ge_2 m H; lia.
Qed.

Definition opp {m} (a : Zstar m) : Zstar m := of_Zmod (Zmod.opp a).

(*
Lemma to_N_one {m} : to_N (@one m) = (1 mod m)%N.
Proof.
  cbv [to_Z one]; rewrite to_N_of_small_coprime_N.
  destruct (Pos.eqb_spec m 1); [|rewrite N.mod_small]; subst; cbn; lia.
Qed.

Lemma to_Z_one {m} : to_Z (@one m) = 1 mod m.
Proof. cbv [to_Z]. rewrite to_N_one, N2Z.inj_mod; trivial. Qed.

Lemma to_Z_opp {m} (a : Zstar m) : to_Z (opp a) = Z.opp (to_Z a) mod m.
Proof. cbv [opp] in *; rewrite to_Z_of_coprime_Z; trivial. Qed.

Lemma opp_to_Zmod {m} a : Zmod.opp (@to_Zmod m a) = to_Zmod (opp a).
Proof.
  apply Zmod.to_Z_inj. rewrite to_Z_to_Zmod, Zmod.to_Z_opp, to_Z_opp; trivial.
Qed.

Lemma opp_opp {m} a : @opp m (opp a) = a.
Proof.
Admitted.

Lemma opp_inj {m} a b (H : @opp m a = opp b) : a = b.
Proof. apply (f_equal opp) in H; rewrite 2 opp_opp in H; trivial. Qed.

Lemma mul_opp_l {m} a b : @mul m (opp a) b = opp (mul a b).
Admitted.

Lemma mul_opp_r {m} a b : @mul m a (opp b) = opp (mul a b).
Admitted.
*)

Lemma opp_1_neq_1 {m : positive} (Hm : 3 <= m) : @opp m one <> one.
Admitted.

Definition eqb {m} (a b : Zstar m) := Zmod.eqb (to_Zmod a) (to_Zmod b).

Lemma eqb_spec {m} a b : BoolSpec (a = b) (a <> b) (@eqb m a b).
Proof.
  cbv [eqb]. case (Zmod.eqb_spec (to_Zmod a) (to_Zmod b));
    constructor; auto using to_Zmod_inj; congruence.
Qed.

Definition sqrt_option {m} (a : Zstar m) :=
  (* TODO: discourage unfolding *)
  List.find (fun r => eqb (mul r r) a) (elements m).

Lemma sqrt_option_Some {m} a r (H : @sqrt_option m a = Some r) : mul r r = a.
Proof.
  cbv [sqrt_option] in *.
  eapply List.find_some in H; case H as [_ H].
  destruct (eqb_spec (mul r r) a); congruence.
Qed.

Lemma sqrt_option_None {m} a (H : @sqrt_option m a = None) :
  ~ exists r, mul r r = a.
Proof.
  cbv [sqrt_option].
  intros [r Hr].
  eapply List.find_none in H; trivial using in_elements.
  rewrite Hr in H.
  destruct (eqb_spec a a); congruence.
Qed.

Definition sqrt {m} (a : Zstar m) :=
  (* TODO: discourage unfolding *)
  match sqrt_option a with Some r => r | _ => one end.

Definition jacobi_symbol {m} (a : Zstar m) : Zstar m :=
  (* TODO: discourage unfolding *)
  match sqrt_option a with Some r => one | _ => opp one end.

Lemma jacobi_symbol_iff {m} a :
  @jacobi_symbol m a = one <-> exists r, mul r r = a.
Proof.
  cbv [jacobi_symbol]; case sqrt_option eqn:H.
  { apply sqrt_option_Some in H; intuition eauto. }
  { apply sqrt_option_None in H; intuition eauto.
    eexists. apply wlog_eq_Zstar_3; intro Hp'.
    instantiate (1:=one). ecase opp_1_neq_1; eauto. }
Qed.

Lemma jacobi_symbol_1 {m} : @jacobi_symbol m one = one.
Proof. eapply jacobi_symbol_iff, ex_intro, mul_1_l. Qed.

Lemma sqrt_unique' {m} (r s : Zstar m) (H : mul r r = mul s s) :
  s = r \/ s = opp r.
Proof.
  eapply (f_equal to_Zmod) in H; rewrite 2 to_Zmod_mul in H.
  eapply factor_equality_of_squares in H.
  destruct (Zmod.eqb_spec (Zmod.sub r s) zero);
    [eapply sub_eq_0, to_Zmod_inj in H0; auto|].
  destruct (Zmod.eqb_spec (Zmod.add r s) zero).
    { eapply add_eq_0 in H1.
      (* rewrite opp_to_Zmod in H1. auto using to_Zmod_inj. } *)
Admitted.

Lemma sqrt_unique {m} (r a : Zstar m) (H : mul r r = a) :
  r = sqrt a \/ r = opp (sqrt a).
Proof.
  cbv [sqrt].
  destruct sqrt_option eqn:Hz; [|exfalso; eapply sqrt_option_None; eauto].
  apply sqrt_option_Some in Hz.
  apply sqrt_unique'; congruence.
Qed.

Import Lists.List. Import ListNotations.
Lemma euler_criterion_lemma  {p : positive} (Hp : prime p) (a : Zstar p) :
  fold_right mul one (elements p) = mul (opp (jacobi_symbol a)) (pow_N a ((p-1)/2)).
Proof.
  apply wlog_eq_Zstar_3; intro Hp'.
  set (xs := elements p).
  set (roots := List.filter (fun x => eqb (div a x) a) xs).
  set (smalls := List.filter (fun x : Zstar _ => (x <? div a x)%N) xs).
  set (larges := List.filter (fun x : Zstar _ => (div a x <? x)%N) xs).
  assert (PP : Permutation (elements p) (smalls ++ larges ++ roots)) by admit.
  rewrite (prod_Permutation _ _ _ PP).
  pose proof @NoDup_elements p. (* TODO @ *)
  assert (NoDup roots) by eauto using NoDup_filter.
  assert (NoDup smalls) by eauto using NoDup_filter.
  assert (NoDup larges) by eauto using NoDup_filter.
  rewrite app_assoc, fold_right_app.
  assert (HP : Permutation smalls (map (fun x : Zstar p => div a x) larges)).
  { apply Permutation.NoDup_Permutation; intros; trivial.
    { eapply FinFun.Injective_map_NoDup; trivial.
      (* TODO: div_inj, inv_inj *)
      intros ? ? E.
      rewrite <-2mul_inv_r in E.
      eapply mul_cancel_l, (f_equal inv) in E.
      rewrite 2 Zstar.inv_inv in E.
      trivial. }
    cbv [smalls larges].
    rewrite in_map_iff; repeat setoid_rewrite filter_In.
    repeat setoid_rewrite N.ltb_lt.
    assert (Hdiv : forall x y z : Zstar p, div z y = x <-> z = mul x y) by admit.
    setoid_rewrite Hdiv.
    split.
    { intros []. exists (div a x).
      replace (mul x (div a x)) with a by admit.
      replace (div a (div a x)) with x by admit.
      auto using in_elements. }
    { intros (y&?&?&?); subst.
      replace (div (mul x y) y) with x in * by admit.
      replace (div (mul x y) x) with y in * by admit.
      split; auto using in_elements with arith. } }
  erewrite fold_right_app, (prod_Permutation _ _ _ HP), <-fold_right_app.
  rewrite (prod_Permutation _ (map _ larges++larges) (List.flat_map (fun x => [div a x; x]) larges)) by admit.
  assert (fold_right_flat_map : forall a f (xs : list (Zstar p)), fold_right mul a (flat_map f xs) = fold_right mul a (map (fun x => fold_right (@mul p) one (f x)) xs)) by admit;
  rewrite fold_right_flat_map; clear fold_right_flat_map.
  erewrite map_ext; cycle 1.
  { intros x. cbn [fold_right]. rewrite mul_1_r, (*TODO: lemma*)<-mul_inv_r, <-mul_assoc, mul_inv_same_l, mul_1_r; exact eq_refl. }

  progress replace (map (fun _ : Zstar p => a) larges) with (repeat a (length larges)) in * by admit.
  assert (fold_right_init_monoid : forall x ys, fold_right mul x ys = mul x (fold_right mul one ys :> Zstar p)) by admit.
  rewrite fold_right_init_monoid, prod_repeat.
  assert (length smalls = length larges).
  { apply Permutation.Permutation_length in HP; rewrite map_length in HP; trivial. }
  replace (N.of_nat (length larges)) with ((p-1-N.of_nat(length roots))/2)%N; cycle 1.
  { eapply Permutation.Permutation_length in PP; rewrite 2app_length in PP.
    rewrite Zstar.length_elements_prime in PP by trivial.
    zify; Z.to_euclidean_division_equations; nia. }
  assert (roots = [] /\ jacobi_symbol a = opp one \/ exists r, roots = [r; opp r] /\ mul r r = a /\ jacobi_symbol a = one) as [[-> s_a] | [? [-> [sqrt_a s_a]]]] by admit.
  all : cbn [length fold_right]; simpl N.of_nat; repeat rewrite ?s_a, ?opp_opp, ?mul_1_l, ?mul_1_r, ?N.sub_0_r, ?mul_opp_r, ?mul_opp_l, ?sqrt_a, <-?pow_N_succ_r; f_equal.

  f_equal; zify; Z.to_euclidean_division_equations; nia.
Admitted.

Theorem wilson_fwd {p : positive} (Hp : prime p) :
  fold_right mul one (elements p) = opp one.
Proof.
  rewrite euler_criterion_lemma with (a:=one), jacobi_symbol_1 by trivial.
  rewrite pow_N_1_l, mul_opp_l, mul_1_l; f_equal.
Qed.

Theorem euler_criterion  {p : positive} (Hp : prime p) (a : Zstar p) :
  pow_N a ((p-1)/2) = jacobi_symbol a.
Proof.
  pose proof euler_criterion_lemma Hp a; rewrite wilson_fwd in *;
  cbv [jacobi_symbol] in *; case sqrt_option in *;
  rewrite ?mul_opp_l, ?mul_1_l, ?opp_opp in *; auto using eq_sym, opp_inj.
Qed.

Module Zmod.
Import Coq.Numbers.Zmod.Base.

Theorem fermat_nz {m} (a : Zmod m) (Ha : a <> zero) (H : prime m) :
  pow_N a (Pos.pred_N m) = one.
Proof.
  case (Zstar.of_Zmod_option a) eqn:Hx; cycle 1.
  { eapply Zstar.of_Zmod_option_None_prime in Hx; congruence. }
  eapply Zstar.of_Zmod_option_Some in Hx; rewrite Hx; clear Hx.
  rewrite <-Zstar.to_Zmod_pow_N, Zstar.fermat, Zstar.to_Zmod_1; trivial.
Qed.

Theorem fermat {m} (a : Zmod m) (H : prime m) : pow_N a m = a.
Proof.
  case (eqb_spec a zero); intros.
  { subst a. rewrite pow_N_0_l; trivial; lia. }
  { replace (N.pos m) with (N.succ (Pos.pred_N m)) by lia.
    rewrite pow_N_succ_r, fermat_nz, mul_1_r; trivial. }
Qed.

Theorem fermat_inv {m} (a : Zmod m) (Ha : a <> zero) (H : prime m) :
  pow_N a (N.pred (Pos.pred_N m)) = inv a.
Proof.
  eapply mul_cancel_l_prime; try eassumption.
  rewrite <-pow_N_succ_r, N.succ_pred, fermat_nz, mul_inv_same_r_prime;
    trivial; pose proof prime_ge_2 m H; lia.
Qed.
End Zmod.

Module N.
Local Open Scope N_scope.
Theorem fermat_nz (m a : N) (Hm : prime m) (Ha : a mod m <> 0) :
  a^(m-1) mod m = 1.
Proof.
  pose proof prime_ge_2 _ Hm; case m as [|m]; try lia; [].
  replace (N.pos m - 1) with (Pos.pred_N m) by lia.
  rewrite <-Zmod.to_N_of_N, Zmod.of_N_pow, Zmod.fermat_nz, Zmod.to_N_1; auto using Zmod.of_N_nz.
Qed.

Theorem fermat (m a : N) (Hm : prime m) : a^m mod m = a mod m.
Proof.
  pose proof prime_ge_2 _ Hm; case m as [|m]; try lia; [].
  rewrite <-2Zmod.to_N_of_N, Zmod.of_N_pow, Zmod.fermat; trivial.
Qed.
End N.

Module Z.
Theorem fermat_nz (m a : Z) (Hm : prime m) (Ha : a mod m <> 0) :
  a^(m-1) mod m = 1.
Proof.
  pose proof prime_ge_2 _ Hm as Hm'.
  pose proof N.fermat_nz (Z.to_N m) (Z.to_N (a mod m)).
  rewrite <-!N2Z.inj_iff, !N2Z.inj_mod, !N2Z.inj_pow, !Z2N.id, Z.mod_mod in H
    by (Z.div_mod_to_equations; lia).
  rewrite N2Z.inj_sub, Z2N.id in H by lia; cbn in H.
  rewrite <-Z.mod_pow_l; eauto.
Qed.

Theorem fermat (m a : Z) (Hm : prime m) : Z.pow a m mod m = a mod m.
Proof.
  pose proof prime_ge_2 _ Hm; case m as [|m|]; try lia; [].
  rewrite <-2Zmod.to_Z_of_Z.
  erewrite <-(Zmod.fermat (Zmod.of_Z m a) Hm).
  rewrite Zmod.of_Z_pow; trivial; lia.
Qed.
End Z.
