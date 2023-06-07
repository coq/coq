(* TODO: move out of Zstar *)

Require Import Coq.Numbers.Zmod.TODO_MOVE.

Require Import Coq.NArith.NArith Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Numbers.Zmod.Base Coq.Numbers.Zmod.Inverse Coq.Numbers.Zstar.Base.
Require Coq.Sorting.Permutation.
Local Notation Permutation := Permutation.Permutation.

Local Open Scope Z_scope.

Import Zmod.Base.Coercions.

Module Zstar.
Lemma prod_Permutation {m} one (xs ys : list (Zstar m)) (H : Permutation xs ys) :
  List.fold_right mul one xs = List.fold_right mul one ys.
Proof. induction H; cbn; repeat rewrite ?mul_assoc, ?(mul_comm x); congruence. Qed.

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
End Zstar.

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
Theorem fermat (m a : Z) (Hm : prime m) : Z.pow a m mod m = a mod m.
Proof.
  pose proof prime_ge_2 _ Hm; case m as [|m|]; try lia; [].
  rewrite <-2Zmod.to_Z_of_Z.
  erewrite <-(Zmod.fermat (Zmod.of_Z m a) Hm).
  rewrite Zmod.of_Z_pow; trivial; lia.
Qed.
End Z.
