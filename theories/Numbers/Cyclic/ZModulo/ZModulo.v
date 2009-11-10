(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(** * Type [Z] viewed modulo a particular constant corresponds to [Z/nZ]
      as defined abstractly in CyclicAxioms. *)

(** Even if the construction provided here is not reused for building
  the efficient arbitrary precision numbers, it provides a simple
  implementation of CyclicAxioms, hence ensuring its coherence. *)

Set Implicit Arguments.

Require Import Bool.
Require Import ZArith.
Require Import Znumtheory.
Require Import BigNumPrelude.
Require Import DoubleType.
Require Import CyclicAxioms.

Local Open Scope Z_scope.

Section ZModulo.

 Variable digits : positive.
 Hypothesis digits_ne_1 : digits <> 1%positive.

 Definition wB := base digits.

 Definition znz := Z.
 Definition znz_digits := digits.
 Definition znz_zdigits := Zpos digits.
 Definition znz_to_Z x := x mod wB.

 Notation "[| x |]" := (znz_to_Z x)  (at level 0, x at level 99).

 Notation "[+| c |]" :=
   (interp_carry 1 wB znz_to_Z c)  (at level 0, x at level 99).

 Notation "[-| c |]" :=
   (interp_carry (-1) wB znz_to_Z c)  (at level 0, x at level 99).

 Notation "[|| x ||]" :=
   (zn2z_to_Z wB znz_to_Z x)  (at level 0, x at level 99).

 Lemma spec_more_than_1_digit: 1 < Zpos digits.
 Proof.
  unfold znz_digits.
  generalize digits_ne_1; destruct digits; auto.
  destruct 1; auto.
 Qed.
 Let digits_gt_1 := spec_more_than_1_digit.

 Lemma wB_pos : wB > 0.
 Proof.
  unfold wB, base; auto with zarith.
 Qed.
 Hint Resolve wB_pos.

 Lemma spec_to_Z_1 : forall x, 0 <= [|x|].
 Proof.
  unfold znz_to_Z; intros; destruct (Z_mod_lt x wB wB_pos); auto.
 Qed.

 Lemma spec_to_Z_2 : forall x, [|x|] < wB.
 Proof.
  unfold znz_to_Z; intros; destruct (Z_mod_lt x wB wB_pos); auto.
 Qed.
 Hint Resolve spec_to_Z_1 spec_to_Z_2.

 Lemma spec_to_Z : forall x, 0 <= [|x|] < wB.
 Proof.
  auto.
 Qed.

 Definition znz_of_pos x :=
   let (q,r) := Zdiv_eucl_POS x wB in (N_of_Z q, r).

 Lemma spec_of_pos : forall p,
   Zpos p = (Z_of_N (fst (znz_of_pos p)))*wB + [|(snd (znz_of_pos p))|].
 Proof.
  intros; unfold znz_of_pos; simpl.
  generalize (Z_div_mod_POS wB wB_pos p).
  destruct (Zdiv_eucl_POS p wB); simpl; destruct 1.
  unfold znz_to_Z; rewrite Zmod_small; auto.
  assert (0 <= z).
   replace z with (Zpos p / wB) by
    (symmetry; apply Zdiv_unique with z0; auto).
   apply Z_div_pos; auto with zarith.
  replace (Z_of_N (N_of_Z z)) with z by
    (destruct z; simpl; auto; elim H1; auto).
  rewrite Zmult_comm; auto.
 Qed.

 Lemma spec_zdigits : [|znz_zdigits|] = Zpos znz_digits.
 Proof.
  unfold znz_to_Z, znz_zdigits, znz_digits.
  apply Zmod_small.
  unfold wB, base.
  split; auto with zarith.
  apply Zpower2_lt_lin; auto with zarith.
 Qed.

 Definition znz_0 := 0.
 Definition znz_1 := 1.
 Definition znz_Bm1 := wB - 1.

 Lemma spec_0 : [|znz_0|] = 0.
 Proof.
  unfold znz_to_Z, znz_0.
  apply Zmod_small; generalize wB_pos; auto with zarith.
 Qed.

 Lemma spec_1 : [|znz_1|] = 1.
 Proof.
  unfold znz_to_Z, znz_1.
  apply Zmod_small; split; auto with zarith.
  unfold wB, base.
  apply Zlt_trans with (Zpos digits); auto.
  apply Zpower2_lt_lin; auto with zarith.
 Qed.

 Lemma spec_Bm1 : [|znz_Bm1|] = wB - 1.
 Proof.
  unfold znz_to_Z, znz_Bm1.
  apply Zmod_small; split; auto with zarith.
  unfold wB, base.
  cut (1 <= 2 ^ Zpos digits); auto with zarith.
  apply Zle_trans with (Zpos digits); auto with zarith.
  apply Zpower2_le_lin; auto with zarith.
 Qed.

 Definition znz_compare x y := Zcompare [|x|] [|y|].

 Lemma spec_compare : forall x y,
       match znz_compare x y with
       | Eq => [|x|] = [|y|]
       | Lt => [|x|] < [|y|]
       | Gt => [|x|] > [|y|]
       end.
 Proof.
  intros; unfold znz_compare, Zlt, Zgt.
  case_eq (Zcompare [|x|] [|y|]); auto.
  intros; apply Zcompare_Eq_eq; auto.
 Qed.

 Definition znz_eq0 x :=
   match [|x|] with Z0 => true | _ => false end.

 Lemma spec_eq0 : forall x, znz_eq0 x = true -> [|x|] = 0.
 Proof.
  unfold znz_eq0; intros; now destruct [|x|].
 Qed.

 Definition znz_opp_c x :=
   if znz_eq0 x then C0 0 else C1 (- x).
 Definition znz_opp x := - x.
 Definition znz_opp_carry x := - x - 1.

 Lemma spec_opp_c : forall x, [-|znz_opp_c x|] = -[|x|].
 Proof.
 intros; unfold znz_opp_c, znz_to_Z; auto.
 case_eq (znz_eq0 x); intros; unfold interp_carry.
 fold [|x|]; rewrite (spec_eq0 x H); auto.
 assert (x mod wB <> 0).
  unfold znz_eq0, znz_to_Z in H.
  intro H0; rewrite H0 in H; discriminate.
 rewrite Z_mod_nz_opp_full; auto with zarith.
 Qed.

 Lemma spec_opp : forall x, [|znz_opp x|] = (-[|x|]) mod wB.
 Proof.
 intros; unfold znz_opp, znz_to_Z; auto.
 change ((- x) mod wB = (0 - (x mod wB)) mod wB).
 rewrite Zminus_mod_idemp_r; simpl; auto.
 Qed.

 Lemma spec_opp_carry : forall x, [|znz_opp_carry x|] = wB - [|x|] - 1.
 Proof.
 intros; unfold znz_opp_carry, znz_to_Z; auto.
 replace (- x - 1) with (- 1 - x) by omega.
 rewrite <- Zminus_mod_idemp_r.
 replace ( -1 - x mod wB) with (0 + ( -1 - x mod wB)) by omega.
 rewrite <- (Z_mod_same_full wB).
 rewrite Zplus_mod_idemp_l.
 replace (wB + (-1 - x mod wB)) with (wB - x mod wB -1) by omega.
 apply Zmod_small.
 generalize (Z_mod_lt x wB wB_pos); omega.
 Qed.

 Definition znz_succ_c x :=
  let y := Zsucc x in
  if znz_eq0 y then C1 0 else C0 y.

 Definition znz_add_c x y :=
  let z := [|x|] + [|y|] in
  if Z_lt_le_dec z wB then C0 z else C1 (z-wB).

 Definition znz_add_carry_c x y :=
  let z := [|x|]+[|y|]+1 in
  if Z_lt_le_dec z wB then C0 z else C1 (z-wB).

 Definition znz_succ := Zsucc.
 Definition znz_add := Zplus.
 Definition znz_add_carry x y := x + y + 1.

 Lemma Zmod_equal :
  forall x y z, z>0 -> (x-y) mod z = 0 -> x mod z = y mod z.
 Proof.
 intros.
 generalize (Z_div_mod_eq (x-y) z H); rewrite H0, Zplus_0_r.
 remember ((x-y)/z) as k.
 intros H1; symmetry in H1; rewrite <- Zeq_plus_swap in H1.
 subst x.
 rewrite Zplus_comm, Zmult_comm, Z_mod_plus; auto.
 Qed.

 Lemma spec_succ_c : forall x, [+|znz_succ_c x|] = [|x|] + 1.
 Proof.
 intros; unfold znz_succ_c, znz_to_Z, Zsucc.
 case_eq (znz_eq0 (x+1)); intros; unfold interp_carry.

 rewrite Zmult_1_l.
 replace (wB + 0 mod wB) with wB by auto with zarith.
 symmetry; rewrite Zeq_plus_swap.
 assert ((x+1) mod wB = 0) by (apply spec_eq0; auto).
 replace (wB-1) with ((wB-1) mod wB) by
  (apply Zmod_small; generalize wB_pos; omega).
 rewrite <- Zminus_mod_idemp_l; rewrite Z_mod_same; simpl; auto.
 apply Zmod_equal; auto.

 assert ((x+1) mod wB <> 0).
  unfold znz_eq0, znz_to_Z in *; now destruct ((x+1) mod wB).
 assert (x mod wB + 1 <> wB).
  contradict H0.
  rewrite Zeq_plus_swap in H0; simpl in H0.
  rewrite <- Zplus_mod_idemp_l; rewrite H0.
  replace (wB-1+1) with wB; auto with zarith; apply Z_mod_same; auto.
 rewrite <- Zplus_mod_idemp_l.
 apply Zmod_small.
 generalize (Z_mod_lt x wB wB_pos); omega.
 Qed.

 Lemma spec_add_c : forall x y, [+|znz_add_c x y|] = [|x|] + [|y|].
 Proof.
 intros; unfold znz_add_c, znz_to_Z, interp_carry.
 destruct Z_lt_le_dec.
 apply Zmod_small;
  generalize (Z_mod_lt x wB wB_pos) (Z_mod_lt y wB wB_pos); omega.
 rewrite Zmult_1_l, Zplus_comm, Zeq_plus_swap.
 apply Zmod_small;
  generalize (Z_mod_lt x wB wB_pos) (Z_mod_lt y wB wB_pos); omega.
 Qed.

 Lemma spec_add_carry_c : forall x y, [+|znz_add_carry_c x y|] = [|x|] + [|y|] + 1.
 Proof.
 intros; unfold znz_add_carry_c, znz_to_Z, interp_carry.
 destruct Z_lt_le_dec.
 apply Zmod_small;
  generalize (Z_mod_lt x wB wB_pos) (Z_mod_lt y wB wB_pos); omega.
 rewrite Zmult_1_l, Zplus_comm, Zeq_plus_swap.
 apply Zmod_small;
  generalize (Z_mod_lt x wB wB_pos) (Z_mod_lt y wB wB_pos); omega.
 Qed.

 Lemma spec_succ : forall x, [|znz_succ x|] = ([|x|] + 1) mod wB.
 Proof.
 intros; unfold znz_succ, znz_to_Z, Zsucc.
 symmetry; apply Zplus_mod_idemp_l.
 Qed.

 Lemma spec_add : forall x y, [|znz_add x y|] = ([|x|] + [|y|]) mod wB.
 Proof.
 intros; unfold znz_add, znz_to_Z; apply Zplus_mod.
 Qed.

 Lemma spec_add_carry :
	 forall x y, [|znz_add_carry x y|] = ([|x|] + [|y|] + 1) mod wB.
 Proof.
 intros; unfold znz_add_carry, znz_to_Z.
 rewrite <- Zplus_mod_idemp_l.
 rewrite (Zplus_mod x y).
 rewrite Zplus_mod_idemp_l; auto.
 Qed.

 Definition znz_pred_c x :=
  if znz_eq0 x then C1 (wB-1) else C0 (x-1).

 Definition znz_sub_c x y :=
  let z := [|x|]-[|y|] in
  if Z_lt_le_dec z 0 then C1 (wB+z) else C0 z.

 Definition znz_sub_carry_c x y :=
  let z := [|x|]-[|y|]-1 in
  if Z_lt_le_dec z 0 then C1 (wB+z) else C0 z.

 Definition znz_pred := Zpred.
 Definition znz_sub := Zminus.
 Definition znz_sub_carry x y := x - y - 1.

 Lemma spec_pred_c : forall x, [-|znz_pred_c x|] = [|x|] - 1.
 Proof.
 intros; unfold znz_pred_c, znz_to_Z, interp_carry.
 case_eq (znz_eq0 x); intros.
 fold [|x|]; rewrite spec_eq0; auto.
 replace ((wB-1) mod wB) with (wB-1); auto with zarith.
 symmetry; apply Zmod_small; generalize wB_pos; omega.

 assert (x mod wB <> 0).
  unfold znz_eq0, znz_to_Z in *; now destruct (x mod wB).
 rewrite <- Zminus_mod_idemp_l.
 apply Zmod_small.
 generalize (Z_mod_lt x wB wB_pos); omega.
 Qed.

 Lemma spec_sub_c : forall x y, [-|znz_sub_c x y|] = [|x|] - [|y|].
 Proof.
 intros; unfold znz_sub_c, znz_to_Z, interp_carry.
 destruct Z_lt_le_dec.
 replace ((wB + (x mod wB - y mod wB)) mod wB) with
   (wB + (x mod wB - y mod wB)).
 omega.
 symmetry; apply Zmod_small.
 generalize wB_pos (Z_mod_lt x wB wB_pos) (Z_mod_lt y wB wB_pos); omega.

 apply Zmod_small.
 generalize wB_pos (Z_mod_lt x wB wB_pos) (Z_mod_lt y wB wB_pos); omega.
 Qed.

 Lemma spec_sub_carry_c : forall x y, [-|znz_sub_carry_c x y|] = [|x|] - [|y|] - 1.
 Proof.
 intros; unfold znz_sub_carry_c, znz_to_Z, interp_carry.
 destruct Z_lt_le_dec.
 replace ((wB + (x mod wB - y mod wB - 1)) mod wB) with
   (wB + (x mod wB - y mod wB -1)).
 omega.
 symmetry; apply Zmod_small.
 generalize wB_pos (Z_mod_lt x wB wB_pos) (Z_mod_lt y wB wB_pos); omega.

 apply Zmod_small.
 generalize wB_pos (Z_mod_lt x wB wB_pos) (Z_mod_lt y wB wB_pos); omega.
 Qed.

 Lemma spec_pred : forall x, [|znz_pred x|] = ([|x|] - 1) mod wB.
 Proof.
 intros; unfold znz_pred, znz_to_Z, Zpred.
 rewrite <- Zplus_mod_idemp_l; auto.
 Qed.

 Lemma spec_sub : forall x y, [|znz_sub x y|] = ([|x|] - [|y|]) mod wB.
 Proof.
 intros; unfold znz_sub, znz_to_Z; apply Zminus_mod.
 Qed.

 Lemma spec_sub_carry :
  forall x y, [|znz_sub_carry x y|] = ([|x|] - [|y|] - 1) mod wB.
 Proof.
 intros; unfold znz_sub_carry, znz_to_Z.
 rewrite <- Zminus_mod_idemp_l.
 rewrite (Zminus_mod x y).
 rewrite Zminus_mod_idemp_l.
 auto.
 Qed.

 Definition znz_mul_c x y :=
  let (h,l) := Zdiv_eucl ([|x|]*[|y|]) wB in
  if znz_eq0 h then if znz_eq0 l then W0 else WW h l else WW h l.

 Definition znz_mul := Zmult.

 Definition znz_square_c x := znz_mul_c x x.

 Lemma spec_mul_c : forall x y, [|| znz_mul_c x y ||] = [|x|] * [|y|].
 Proof.
 intros; unfold znz_mul_c, zn2z_to_Z.
 assert (Zdiv_eucl ([|x|]*[|y|]) wB = (([|x|]*[|y|])/wB,([|x|]*[|y|]) mod wB)).
  unfold Zmod, Zdiv; destruct Zdiv_eucl; auto.
 generalize (Z_div_mod ([|x|]*[|y|]) wB wB_pos); destruct Zdiv_eucl as (h,l).
 destruct 1; injection H; clear H; intros.
 rewrite H0.
 assert ([|l|] = l).
  apply Zmod_small; auto.
 assert ([|h|] = h).
  apply Zmod_small.
  subst h.
  split.
  apply Z_div_pos; auto with zarith.
  apply Zdiv_lt_upper_bound; auto with zarith.
  apply Zmult_lt_compat; auto with zarith.
 clear H H0 H1 H2.
 case_eq (znz_eq0 h); simpl; intros.
 case_eq (znz_eq0 l); simpl; intros.
 rewrite <- H3, <- H4, (spec_eq0 h), (spec_eq0 l); auto with zarith.
 rewrite H3, H4; auto with zarith.
 rewrite H3, H4; auto with zarith.
 Qed.

 Lemma spec_mul : forall x y, [|znz_mul x y|] = ([|x|] * [|y|]) mod wB.
 Proof.
 intros; unfold znz_mul, znz_to_Z; apply Zmult_mod.
 Qed.

 Lemma spec_square_c : forall x, [|| znz_square_c x||] = [|x|] * [|x|].
 Proof.
 intros x; exact (spec_mul_c x x).
 Qed.

 Definition znz_div x y := Zdiv_eucl [|x|] [|y|].

 Lemma spec_div : forall a b, 0 < [|b|] ->
      let (q,r) := znz_div a b in
      [|a|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|].
 Proof.
 intros; unfold znz_div.
 assert ([|b|]>0) by auto with zarith.
 assert (Zdiv_eucl [|a|] [|b|] = ([|a|]/[|b|], [|a|] mod [|b|])).
  unfold Zmod, Zdiv; destruct Zdiv_eucl; auto.
 generalize (Z_div_mod [|a|] [|b|] H0).
 destruct Zdiv_eucl as (q,r); destruct 1; intros.
 injection H1; clear H1; intros.
 assert ([|r|]=r).
  apply Zmod_small; generalize (Z_mod_lt b wB wB_pos); fold [|b|];
   auto with zarith.
 assert ([|q|]=q).
  apply Zmod_small.
  subst q.
  split.
  apply Z_div_pos; auto with zarith.
  apply Zdiv_lt_upper_bound; auto with zarith.
  apply Zlt_le_trans with (wB*1).
  rewrite Zmult_1_r; auto with zarith.
  apply Zmult_le_compat; generalize wB_pos; auto with zarith.
 rewrite H5, H6; rewrite Zmult_comm; auto with zarith.
 Qed.

 Definition znz_div_gt := znz_div.

 Lemma spec_div_gt : forall a b, [|a|] > [|b|] -> 0 < [|b|] ->
      let (q,r) := znz_div_gt a b in
      [|a|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|].
 Proof.
 intros.
 apply spec_div; auto.
 Qed.

 Definition znz_mod x y := [|x|] mod [|y|].
 Definition znz_mod_gt x y := [|x|] mod [|y|].

 Lemma spec_mod :  forall a b, 0 < [|b|] ->
      [|znz_mod a b|] = [|a|] mod [|b|].
 Proof.
 intros; unfold znz_mod.
 apply Zmod_small.
 assert ([|b|]>0) by auto with zarith.
 generalize (Z_mod_lt [|a|] [|b|] H0) (Z_mod_lt b wB wB_pos).
 fold [|b|]; omega.
 Qed.

 Lemma spec_mod_gt : forall a b, [|a|] > [|b|] -> 0 < [|b|] ->
      [|znz_mod_gt a b|] = [|a|] mod [|b|].
 Proof.
 intros; apply spec_mod; auto.
 Qed.

 Definition znz_gcd x y := Zgcd [|x|] [|y|].
 Definition znz_gcd_gt x y := Zgcd [|x|] [|y|].

 Lemma Zgcd_bound : forall a b, 0<=a -> 0<=b -> Zgcd a b <= Zmax a b.
 Proof.
 intros.
 generalize (Zgcd_is_gcd a b); inversion_clear 1.
 destruct H2; destruct H3; clear H4.
 assert (H3:=Zgcd_is_pos a b).
 destruct (Z_eq_dec (Zgcd a b) 0).
 rewrite e; generalize (Zmax_spec a b); omega.
 assert (0 <= q).
  apply Zmult_le_reg_r with (Zgcd a b); auto with zarith.
 destruct (Z_eq_dec q 0).

 subst q; simpl in *; subst a; simpl; auto.
 generalize (Zmax_spec 0 b) (Zabs_spec b); omega.

 apply Zle_trans with a.
 rewrite H1 at 2.
 rewrite <- (Zmult_1_l (Zgcd a b)) at 1.
 apply Zmult_le_compat; auto with zarith.
 generalize (Zmax_spec a b); omega.
 Qed.

 Lemma spec_gcd : forall a b, Zis_gcd [|a|] [|b|] [|znz_gcd a b|].
 Proof.
 intros; unfold znz_gcd.
 generalize (Z_mod_lt a wB wB_pos)(Z_mod_lt b wB wB_pos); intros.
 fold [|a|] in *; fold [|b|] in *.
 replace ([|Zgcd [|a|] [|b|]|]) with (Zgcd [|a|] [|b|]).
 apply Zgcd_is_gcd.
 symmetry; apply Zmod_small.
 split.
 apply Zgcd_is_pos.
 apply Zle_lt_trans with (Zmax [|a|] [|b|]).
 apply Zgcd_bound; auto with zarith.
 generalize (Zmax_spec [|a|] [|b|]); omega.
 Qed.

 Lemma spec_gcd_gt : forall a b, [|a|] > [|b|] ->
      Zis_gcd [|a|] [|b|] [|znz_gcd_gt a b|].
 Proof.
  intros. apply spec_gcd; auto.
 Qed.

 Definition znz_div21 a1 a2 b :=
  Zdiv_eucl ([|a1|]*wB+[|a2|]) [|b|].

 Lemma spec_div21 : forall a1 a2 b,
      wB/2 <= [|b|] ->
      [|a1|] < [|b|] ->
      let (q,r) := znz_div21 a1 a2 b in
      [|a1|] *wB+ [|a2|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|].
 Proof.
 intros; unfold znz_div21.
 generalize (Z_mod_lt a1 wB wB_pos); fold [|a1|]; intros.
 generalize (Z_mod_lt a2 wB wB_pos); fold [|a2|]; intros.
 assert ([|b|]>0) by auto with zarith.
 remember ([|a1|]*wB+[|a2|]) as a.
 assert (Zdiv_eucl a [|b|] = (a/[|b|], a mod [|b|])).
  unfold Zmod, Zdiv; destruct Zdiv_eucl; auto.
 generalize (Z_div_mod a [|b|] H3).
 destruct Zdiv_eucl as (q,r); destruct 1; intros.
 injection H4; clear H4; intros.
 assert ([|r|]=r).
  apply Zmod_small; generalize (Z_mod_lt b wB wB_pos); fold [|b|];
   auto with zarith.
 assert ([|q|]=q).
  apply Zmod_small.
  subst q.
  split.
  apply Z_div_pos; auto with zarith.
  subst a; auto with zarith.
  apply Zdiv_lt_upper_bound; auto with zarith.
  subst a.
  replace (wB*[|b|]) with (([|b|]-1)*wB + wB) by ring.
  apply Zlt_le_trans with ([|a1|]*wB+wB); auto with zarith.
 rewrite H8, H9; rewrite Zmult_comm; auto with zarith.
 Qed.

 Definition znz_add_mul_div p x y :=
   ([|x|] * (2 ^ [|p|]) + [|y|] / (2 ^ ((Zpos znz_digits) - [|p|]))).
 Lemma spec_add_mul_div : forall x y p,
       [|p|] <= Zpos znz_digits ->
       [| znz_add_mul_div p x y |] =
         ([|x|] * (2 ^ [|p|]) +
          [|y|] / (2 ^ ((Zpos znz_digits) - [|p|]))) mod wB.
 Proof.
 intros; unfold znz_add_mul_div; auto.
 Qed.

 Definition znz_pos_mod p w := [|w|] mod (2 ^ [|p|]).
 Lemma spec_pos_mod : forall w p,
       [|znz_pos_mod p w|] = [|w|] mod (2 ^ [|p|]).
 Proof.
 intros; unfold znz_pos_mod.
 apply Zmod_small.
 generalize (Z_mod_lt [|w|] (2 ^ [|p|])); intros.
 split.
 destruct H; auto with zarith.
 apply Zle_lt_trans with [|w|]; auto with zarith.
 apply Zmod_le; auto with zarith.
 Qed.

 Definition znz_is_even x :=
   if Z_eq_dec ([|x|] mod 2) 0 then true else false.

 Lemma spec_is_even : forall x,
      if znz_is_even x then [|x|] mod 2 = 0 else [|x|] mod 2 = 1.
 Proof.
 intros; unfold znz_is_even; destruct Z_eq_dec; auto.
 generalize (Z_mod_lt [|x|] 2); omega.
 Qed.

 Definition znz_sqrt x := Zsqrt_plain [|x|].
 Lemma spec_sqrt : forall x,
       [|znz_sqrt x|] ^ 2 <= [|x|] < ([|znz_sqrt x|] + 1) ^ 2.
 Proof.
 intros.
 unfold znz_sqrt.
 repeat rewrite Zpower_2.
 replace [|Zsqrt_plain [|x|]|] with (Zsqrt_plain [|x|]).
 apply Zsqrt_interval; auto with zarith.
 symmetry; apply Zmod_small.
 split.
 apply Zsqrt_plain_is_pos; auto with zarith.

 cut (Zsqrt_plain [|x|] <= (wB-1)); try omega.
 rewrite <- (Zsqrt_square_id (wB-1)).
 apply Zsqrt_le.
 split; auto.
 apply Zle_trans with (wB-1); auto with zarith.
 generalize (spec_to_Z x); auto with zarith.
 apply Zsquare_le.
 generalize wB_pos; auto with zarith.
 Qed.

 Definition znz_sqrt2 x y :=
  let z := [|x|]*wB+[|y|] in
  match z with
   | Z0 => (0, C0 0)
   | Zpos p =>
      let (s,r,_,_) := sqrtrempos p in
      (s, if Z_lt_le_dec r wB then C0 r else C1 (r-wB))
   | Zneg _ => (0, C0 0)
  end.

 Lemma spec_sqrt2 : forall x y,
       wB/ 4 <= [|x|] ->
       let (s,r) := znz_sqrt2 x y in
          [||WW x y||] = [|s|] ^ 2 + [+|r|] /\
          [+|r|] <= 2 * [|s|].
 Proof.
 intros; unfold znz_sqrt2.
 simpl zn2z_to_Z.
 remember ([|x|]*wB+[|y|]) as z.
 destruct z.
 auto with zarith.
 destruct sqrtrempos; intros.
 assert (s < wB).
  destruct (Z_lt_le_dec s wB); auto.
  assert (wB * wB <= Zpos p).
   rewrite e.
   apply Zle_trans with (s*s); try omega.
   apply Zmult_le_compat; generalize wB_pos; auto with zarith.
  assert (Zpos p < wB*wB).
   rewrite Heqz.
   replace (wB*wB) with ((wB-1)*wB+wB) by ring.
   apply Zplus_le_lt_compat; auto with zarith.
   apply Zmult_le_compat; auto with zarith.
   generalize (spec_to_Z x); auto with zarith.
   generalize wB_pos; auto with zarith.
  omega.
 replace [|s|] with s by (symmetry; apply Zmod_small; auto with zarith).
 destruct Z_lt_le_dec; unfold interp_carry.
 replace [|r|] with r by (symmetry; apply Zmod_small; auto with zarith).
 rewrite Zpower_2; auto with zarith.
 replace [|r-wB|] with (r-wB) by (symmetry; apply Zmod_small; auto with zarith).
 rewrite Zpower_2; omega.

 assert (0<=Zneg p).
  rewrite Heqz; generalize wB_pos; auto with zarith.
 compute in H0; elim H0; auto.
 Qed.

 Lemma two_p_power2 : forall x, x>=0 -> two_p x = 2 ^ x.
 Proof.
 intros.
 unfold two_p.
 destruct x; simpl; auto.
 apply two_power_pos_correct.
 Qed.

 Definition znz_head0 x := match [|x|] with
   | Z0 => znz_zdigits
   | Zpos p => znz_zdigits - log_inf p - 1
   | _ => 0
  end.

 Lemma spec_head00:  forall x, [|x|] = 0 -> [|znz_head0 x|] = Zpos znz_digits.
 Proof.
  unfold znz_head0; intros.
  rewrite H; simpl.
  apply spec_zdigits.
 Qed.

 Lemma log_inf_bounded : forall x p, Zpos x < 2^p -> log_inf x < p.
 Proof.
 induction x; simpl; intros.

 assert (0 < p) by (destruct p; compute; auto with zarith; discriminate).
 cut (log_inf x < p - 1); [omega| ].
 apply IHx.
 change (Zpos x~1) with (2*(Zpos x)+1) in H.
 replace p with (Zsucc (p-1)) in H; auto with zarith.
 rewrite Zpower_Zsucc in H; auto with zarith.

 assert (0 < p) by (destruct p; compute; auto with zarith; discriminate).
 cut (log_inf x < p - 1); [omega| ].
 apply IHx.
 change (Zpos x~0) with (2*(Zpos x)) in H.
 replace p with (Zsucc (p-1)) in H; auto with zarith.
 rewrite Zpower_Zsucc in H; auto with zarith.

 simpl; intros; destruct p; compute; auto with zarith.
 Qed.


 Lemma spec_head0  : forall x,  0 < [|x|] ->
	 wB/ 2 <= 2 ^ ([|znz_head0 x|]) * [|x|] < wB.
 Proof.
 intros; unfold znz_head0.
 generalize (spec_to_Z x).
 destruct [|x|]; try discriminate.
 intros.
 destruct (log_inf_correct p).
 rewrite 2 two_p_power2 in H2; auto with zarith.
 assert (0 <= znz_zdigits - log_inf p - 1 < wB).
  split.
  cut (log_inf p < znz_zdigits); try omega.
  unfold znz_zdigits.
  unfold wB, base in *.
  apply log_inf_bounded; auto with zarith.
  apply Zlt_trans with znz_zdigits.
  omega.
  unfold znz_zdigits, wB, base; apply Zpower2_lt_lin; auto with zarith.

 unfold znz_to_Z; rewrite (Zmod_small _ _ H3).
 destruct H2.
 split.
 apply Zle_trans with (2^(znz_zdigits - log_inf p - 1)*(2^log_inf p)).
 apply Zdiv_le_upper_bound; auto with zarith.
 rewrite <- Zpower_exp; auto with zarith.
 rewrite Zmult_comm; rewrite <- Zpower_Zsucc; auto with zarith.
 replace (Zsucc (znz_zdigits - log_inf p -1 +log_inf p)) with znz_zdigits
   by ring.
 unfold wB, base, znz_zdigits; auto with zarith.
 apply Zmult_le_compat; auto with zarith.

 apply Zlt_le_trans
   with (2^(znz_zdigits - log_inf p - 1)*(2^(Zsucc (log_inf p)))).
 apply Zmult_lt_compat_l; auto with zarith.
 rewrite <- Zpower_exp; auto with zarith.
 replace (znz_zdigits - log_inf p -1 +Zsucc (log_inf p)) with znz_zdigits
   by ring.
 unfold wB, base, znz_zdigits; auto with zarith.
 Qed.

 Fixpoint Ptail p := match p with
  | xO p => (Ptail p)+1
  | _ => 0
 end.

 Lemma Ptail_pos : forall p, 0 <= Ptail p.
 Proof.
 induction p; simpl; auto with zarith.
 Qed.
 Hint Resolve Ptail_pos.

 Lemma Ptail_bounded : forall p d, Zpos p < 2^(Zpos d) -> Ptail p < Zpos d.
 Proof.
 induction p; try (compute; auto; fail).
 intros; simpl.
 assert (d <> xH).
  intro; subst.
  compute in H; destruct p; discriminate.
 assert (Zsucc (Zpos (Ppred d)) = Zpos d).
  simpl; f_equal.
  rewrite <- Pplus_one_succ_r.
  destruct (Psucc_pred d); auto.
  rewrite H1 in H0; elim H0; auto.
 assert (Ptail p < Zpos (Ppred d)).
  apply IHp.
  apply Zmult_lt_reg_r with 2; auto with zarith.
  rewrite (Zmult_comm (Zpos p)).
  change (2 * Zpos p) with (Zpos p~0).
  rewrite Zmult_comm.
  rewrite <- Zpower_Zsucc; auto with zarith.
  rewrite H1; auto.
 rewrite <- H1; omega.
 Qed.

 Definition znz_tail0 x :=
  match [|x|] with
   | Z0 => znz_zdigits
   | Zpos p => Ptail p
   | Zneg _ => 0
  end.

 Lemma spec_tail00:  forall x, [|x|] = 0 -> [|znz_tail0 x|] = Zpos znz_digits.
 Proof.
  unfold znz_tail0; intros.
  rewrite H; simpl.
  apply spec_zdigits.
 Qed.

 Lemma spec_tail0  : forall x, 0 < [|x|] ->
         exists y, 0 <= y /\ [|x|] = (2 * y + 1) * (2 ^ [|znz_tail0 x|]).
 Proof.
 intros; unfold znz_tail0.
 generalize (spec_to_Z x).
 destruct [|x|]; try discriminate; intros.
 assert ([|Ptail p|] = Ptail p).
  apply Zmod_small.
  split; auto.
  unfold wB, base in *.
  apply Zlt_trans with (Zpos digits).
  apply Ptail_bounded; auto with zarith.
  apply Zpower2_lt_lin; auto with zarith.
 rewrite H1.

 clear; induction p.
 exists (Zpos p); simpl; rewrite Pmult_1_r; auto with zarith.
 destruct IHp as (y & Yp & Ye).
 exists y.
 split; auto.
 change (Zpos p~0) with (2*Zpos p).
 rewrite Ye.
 change (Ptail p~0) with (Zsucc (Ptail p)).
 rewrite Zpower_Zsucc; auto; ring.

 exists 0; simpl; auto with zarith.
 Qed.

 (** Let's now group everything in two records *)

 Definition zmod_op := mk_znz_op
    (znz_digits : positive)
    (znz_zdigits: znz)
    (znz_to_Z   : znz -> Z)
    (znz_of_pos : positive -> N * znz)
    (znz_head0  : znz -> znz)
    (znz_tail0  : znz -> znz)

    (znz_0   : znz)
    (znz_1   : znz)
    (znz_Bm1 : znz)

    (znz_compare     : znz -> znz -> comparison)
    (znz_eq0         : znz -> bool)

    (znz_opp_c       : znz -> carry znz)
    (znz_opp         : znz -> znz)
    (znz_opp_carry   : znz -> znz)

    (znz_succ_c      : znz -> carry znz)
    (znz_add_c       : znz -> znz -> carry znz)
    (znz_add_carry_c : znz -> znz -> carry znz)
    (znz_succ        : znz -> znz)
    (znz_add         : znz -> znz -> znz)
    (znz_add_carry   : znz -> znz -> znz)

    (znz_pred_c      : znz -> carry znz)
    (znz_sub_c       : znz -> znz -> carry znz)
    (znz_sub_carry_c : znz -> znz -> carry znz)
    (znz_pred        : znz -> znz)
    (znz_sub         : znz -> znz -> znz)
    (znz_sub_carry   : znz -> znz -> znz)

    (znz_mul_c       : znz -> znz -> zn2z znz)
    (znz_mul         : znz -> znz -> znz)
    (znz_square_c    : znz -> zn2z znz)

    (znz_div21       : znz -> znz -> znz -> znz*znz)
    (znz_div_gt      : znz -> znz -> znz * znz)
    (znz_div         : znz -> znz -> znz * znz)

    (znz_mod_gt      : znz -> znz -> znz)
    (znz_mod         : znz -> znz -> znz)

    (znz_gcd_gt      : znz -> znz -> znz)
    (znz_gcd         : znz -> znz -> znz)
    (znz_add_mul_div : znz -> znz -> znz -> znz)
    (znz_pos_mod     : znz -> znz -> znz)

    (znz_is_even     : znz -> bool)
    (znz_sqrt2       : znz -> znz -> znz * carry znz)
    (znz_sqrt        : znz -> znz).

 Definition zmod_spec := mk_znz_spec zmod_op
    spec_to_Z
    spec_of_pos
    spec_zdigits
    spec_more_than_1_digit

    spec_0
    spec_1
    spec_Bm1

    spec_compare
    spec_eq0

    spec_opp_c
    spec_opp
    spec_opp_carry

    spec_succ_c
    spec_add_c
    spec_add_carry_c
    spec_succ
    spec_add
    spec_add_carry

    spec_pred_c
    spec_sub_c
    spec_sub_carry_c
    spec_pred
    spec_sub
    spec_sub_carry

    spec_mul_c
    spec_mul
    spec_square_c

    spec_div21
    spec_div_gt
    spec_div

    spec_mod_gt
    spec_mod

    spec_gcd_gt
    spec_gcd

    spec_head00
    spec_head0
    spec_tail00
    spec_tail0

    spec_add_mul_div
    spec_pos_mod

    spec_is_even
    spec_sqrt2
    spec_sqrt.

End ZModulo.

(** A modular version of the previous construction. *)

Module Type PositiveNotOne.
 Parameter p : positive.
 Axiom not_one : p<> 1%positive.
End PositiveNotOne.

Module ZModuloCyclicType (P:PositiveNotOne) <: CyclicType.
 Definition w := Z.
 Definition w_op := zmod_op P.p.
 Definition w_spec := zmod_spec P.not_one.
End ZModuloCyclicType.

