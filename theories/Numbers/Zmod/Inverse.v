Require Import Coq.Numbers.Zmod.TODO_MOVE. Import TODO_MOVE.Znumtheory.

Require Import Coq.NArith.NArith Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.ZArith.Znumtheory.

Require Import Coq.Numbers.Zstar.Base.
Require Import Coq.Numbers.Zmod.Base.

Local Open Scope Z_scope.
Import Zmod.Base.Coercions.

Module Import Zstar. (* TODO: can we do better than this path hack? *)
  Include Zstar.Base.
End Zstar.

Module Import Zmod. (* TODO: can we do better than this path hack? *)
  Include Zmod.Base.
End Zmod.

Lemma div_same {m} (a : Zmod m) : ndiv a a = of_Z m (Z.gcd a m).
Proof.
  rewrite <-mul_inv_l. apply to_Z_inj. rewrite to_Z_mul, to_Z_inv,
    Z.mul_mod_idemp_l, to_Z_of_Z, invmod_ok by inversion 1; trivial.
Qed.

Definition invertibles m : list (Zmod m) := List.map Zstar.to_Zmod (Zstar.elements m).

Lemma in_invertibles m (x : Zmod m) : List.In x (invertibles m) <-> Z.gcd x m = 1.
Proof.
  cbv [invertibles].
  rewrite List.in_map_iff.
  setoid_rewrite
    ( ltac:(intuition eauto using Zstar.in_elements)
    : forall (m : positive) (x : Zstar m), List.In x (Zstar.elements m) <-> True).
  firstorder subst; trivial using Zstar.coprime_to_Zmod.
  unshelve (eexists; rewrite Zstar.to_Zmod_of_Zmod); eauto.
Qed.

Lemma NoDup_invertibles {m} : List.NoDup (invertibles m).
Proof. apply FinFun.Injective_map_NoDup, Zstar.NoDup_elements. cbv [FinFun.Injective]; auto using Zstar.to_Zmod_inj. Qed.

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
Proof.
  pose proof Zstar.mul_inv_same_l (Zstar.of_Zmod x) as E.
  apply (f_equal Zstar.to_Zmod) in E.
  rewrite Zstar.to_Zmod_mul, Zstar.to_Zmod_inv, Zstar.to_Zmod_of_Zmod, Zstar.to_Zmod_1 in E by trivial; exact E.
Qed.

Lemma mul_inv_same_r_coprime {m} (x : Zmod m) (H : Z.gcd x m = 1) :
  mul x (inv x) = one.
Proof. rewrite mul_comm, mul_inv_same_l_coprime; trivial. Qed.

Lemma mul_inv_same_l_prime {m} (x : Zmod m) (Hm : prime m) (H : x <> zero) :
  mul (inv x) x = one.
Proof. intros; rewrite ?mul_inv_l, ?div_same_prime; trivial. Qed.

Lemma mul_inv_same_r_prime {m} (x : Zmod m) (Hm : prime m) (H : x <> zero) :
  mul x (inv x) = one.
Proof. rewrite mul_comm, mul_inv_same_l_prime; trivial. Qed.

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

Lemma inv_inv {m} (x : Zmod m) (H : Z.gcd x m = 1): inv (inv x) = x.
Proof.
  pose proof Zstar.inv_inv (Zstar.of_Zmod x) as E.
  apply (f_equal Zstar.to_Zmod) in E.
  rewrite 2Zstar.to_Zmod_inv, Zstar.to_Zmod_of_Zmod in E by trivial; exact E.
Qed.

Lemma inv_inv_prime {m} (x : Zmod m) (Hm : prime m): inv (inv x) = x.
Proof.
  case (eqb_spec x zero) as [|Hx]; subst.
  { apply to_Z_inj. rewrite to_Z_inv, invmod_0_l; trivial. }
  pose proof to_Z_nz x ltac:(trivial); pose proof to_Z_range x.
  apply inv_inv, Zgcd_1_rel_prime, rel_prime_le_prime; trivial; lia.
Qed.

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
