(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Type [Z] viewed modulo a particular constant corresponds to [Z/nZ]
      as defined abstractly in CyclicAxioms. *)

(** Even if the construction provided here is not reused for building
  the efficient arbitrary precision numbers, it provides a simple
  implementation of CyclicAxioms, hence ensuring its coherence. *)

Set Implicit Arguments.

Require Import Bool.
Require Import ZArith.
Require Import Znumtheory.
Require Import Zpow_facts.
Require Import DoubleType.
Require Import CyclicAxioms.

Local Open Scope Z_scope.

Section ZModulo.

 Variable digits : positive.
 Hypothesis digits_ne_1 : digits <> 1%positive.

 Definition wB := base digits.

 Definition t := Z.
 Definition zdigits := Zpos digits.
 Definition to_Z x := x mod wB.

 Notation "[| x |]" := (to_Z x)  (at level 0, x at level 99).

 Notation "[+| c |]" :=
   (interp_carry 1 wB to_Z c)  (at level 0, c at level 99).

 Notation "[-| c |]" :=
   (interp_carry (-1) wB to_Z c)  (at level 0, c at level 99).

 Notation "[|| x ||]" :=
   (zn2z_to_Z wB to_Z x)  (at level 0, x at level 99).

 Lemma spec_more_than_1_digit: 1 < Zpos digits.
 Proof.
  generalize digits_ne_1; destruct digits; red; auto.
  destruct 1; auto.
 Qed.
 Let digits_gt_1 := spec_more_than_1_digit.

 Lemma wB_pos : wB > 0.
 Proof.
  apply Z.lt_gt.
  unfold wB, base; auto with zarith.
 Qed.
 Hint Resolve wB_pos.

 Lemma spec_to_Z_1 : forall x, 0 <= [|x|].
 Proof.
  unfold to_Z; intros; destruct (Z_mod_lt x wB wB_pos); auto.
 Qed.

 Lemma spec_to_Z_2 : forall x, [|x|] < wB.
 Proof.
  unfold to_Z; intros; destruct (Z_mod_lt x wB wB_pos); auto.
 Qed.
 Hint Resolve spec_to_Z_1 spec_to_Z_2.

 Lemma spec_to_Z : forall x, 0 <= [|x|] < wB.
 Proof.
  auto.
 Qed.

 Definition of_pos x :=
   let (q,r) := Z.pos_div_eucl x wB in (N_of_Z q, r).

 Lemma spec_of_pos : forall p,
   Zpos p = (Z.of_N (fst (of_pos p)))*wB + [|(snd (of_pos p))|].
 Proof.
  intros; unfold of_pos; simpl.
  generalize (Z_div_mod_POS wB wB_pos p).
  destruct (Z.pos_div_eucl p wB); simpl; destruct 1.
  unfold to_Z; rewrite Zmod_small; auto.
  assert (0 <= z).
   replace z with (Zpos p / wB) by
    (symmetry; apply Zdiv_unique with z0; auto).
   apply Z_div_pos; auto with zarith.
  replace (Z.of_N (N_of_Z z)) with z by
    (destruct z; simpl; auto; elim H1; auto).
  rewrite Z.mul_comm; auto.
 Qed.

 Lemma spec_zdigits : [|zdigits|] = Zpos digits.
 Proof.
  unfold to_Z, zdigits.
  apply Zmod_small.
  unfold wB, base.
  split; auto with zarith.
  apply Zpower2_lt_lin; auto with zarith.
 Qed.

 Definition zero := 0.
 Definition one := 1.
 Definition minus_one := wB - 1.

 Lemma spec_0 : [|zero|] = 0.
 Proof.
  unfold to_Z, zero.
  apply Zmod_small; generalize wB_pos; auto with zarith.
 Qed.

 Lemma spec_1 : [|one|] = 1.
 Proof.
  unfold to_Z, one.
  apply Zmod_small; split; auto with zarith.
  unfold wB, base.
  apply Z.lt_trans with (Zpos digits); auto.
  apply Zpower2_lt_lin; auto with zarith.
 Qed.

 Lemma spec_Bm1 : [|minus_one|] = wB - 1.
 Proof.
  unfold to_Z, minus_one.
  apply Zmod_small; split; auto with zarith.
  unfold wB, base.
  cut (1 <= 2 ^ Zpos digits); auto with zarith.
  apply Z.le_trans with (Zpos digits); auto with zarith.
  apply Zpower2_le_lin; auto with zarith.
 Qed.

 Definition compare x y := Z.compare [|x|] [|y|].

 Lemma spec_compare : forall x y,
   compare x y = Z.compare [|x|] [|y|].
 Proof. reflexivity. Qed.

 Definition eq0 x :=
   match [|x|] with Z0 => true | _ => false end.

 Lemma spec_eq0 : forall x, eq0 x = true -> [|x|] = 0.
 Proof.
  unfold eq0; intros; now destruct [|x|].
 Qed.

 Definition opp_c x :=
   if eq0 x then C0 0 else C1 (- x).
 Definition opp x := - x.
 Definition opp_carry x := - x - 1.

 Lemma spec_opp_c : forall x, [-|opp_c x|] = -[|x|].
 Proof.
 intros; unfold opp_c, to_Z; auto.
 case_eq (eq0 x); intros; unfold interp_carry.
 fold [|x|]; rewrite (spec_eq0 x H); auto.
 assert (x mod wB <> 0).
  unfold eq0, to_Z in H.
  intro H0; rewrite H0 in H; discriminate.
 rewrite Z_mod_nz_opp_full; auto with zarith.
 Qed.

 Lemma spec_opp : forall x, [|opp x|] = (-[|x|]) mod wB.
 Proof.
 intros; unfold opp, to_Z; auto.
 change ((- x) mod wB = (0 - (x mod wB)) mod wB).
 rewrite Zminus_mod_idemp_r; simpl; auto.
 Qed.

 Lemma spec_opp_carry : forall x, [|opp_carry x|] = wB - [|x|] - 1.
 Proof.
 intros; unfold opp_carry, to_Z; auto.
 replace (- x - 1) with (- 1 - x) by omega.
 rewrite <- Zminus_mod_idemp_r.
 replace ( -1 - x mod wB) with (0 + ( -1 - x mod wB)) by omega.
 rewrite <- (Z_mod_same_full wB).
 rewrite Zplus_mod_idemp_l.
 replace (wB + (-1 - x mod wB)) with (wB - x mod wB -1) by omega.
 apply Zmod_small.
 generalize (Z_mod_lt x wB wB_pos); omega.
 Qed.

 Definition succ_c x :=
  let y := Z.succ x in
  if eq0 y then C1 0 else C0 y.

 Definition add_c x y :=
  let z := [|x|] + [|y|] in
  if Z_lt_le_dec z wB then C0 z else C1 (z-wB).

 Definition add_carry_c x y :=
  let z := [|x|]+[|y|]+1 in
  if Z_lt_le_dec z wB then C0 z else C1 (z-wB).

 Definition succ := Z.succ.
 Definition add := Z.add.
 Definition add_carry x y := x + y + 1.

 Lemma Zmod_equal :
  forall x y z, z>0 -> (x-y) mod z = 0 -> x mod z = y mod z.
 Proof.
 intros.
 generalize (Z_div_mod_eq (x-y) z H); rewrite H0, Z.add_0_r.
 remember ((x-y)/z) as k.
 rewrite Z.sub_move_r, Z.add_comm, Z.mul_comm. intros ->.
 now apply Z_mod_plus.
 Qed.

 Lemma spec_succ_c : forall x, [+|succ_c x|] = [|x|] + 1.
 Proof.
 intros; unfold succ_c, to_Z, Z.succ.
 case_eq (eq0 (x+1)); intros; unfold interp_carry.

 rewrite Z.mul_1_l.
 replace (wB + 0 mod wB) with wB by auto with zarith.
 symmetry. rewrite Z.add_move_r.
 assert ((x+1) mod wB = 0) by (apply spec_eq0; auto).
 replace (wB-1) with ((wB-1) mod wB) by
  (apply Zmod_small; generalize wB_pos; omega).
 rewrite <- Zminus_mod_idemp_l; rewrite Z_mod_same; simpl; auto.
 apply Zmod_equal; auto.

 assert ((x+1) mod wB <> 0).
  unfold eq0, to_Z in *; now destruct ((x+1) mod wB).
 assert (x mod wB + 1 <> wB).
  contradict H0.
  rewrite Z.add_move_r in H0; simpl in H0.
  rewrite <- Zplus_mod_idemp_l; rewrite H0.
  replace (wB-1+1) with wB; auto with zarith; apply Z_mod_same; auto.
 rewrite <- Zplus_mod_idemp_l.
 apply Zmod_small.
 generalize (Z_mod_lt x wB wB_pos); omega.
 Qed.

 Lemma spec_add_c : forall x y, [+|add_c x y|] = [|x|] + [|y|].
 Proof.
 intros; unfold add_c, to_Z, interp_carry.
 destruct Z_lt_le_dec.
 apply Zmod_small;
  generalize (Z_mod_lt x wB wB_pos) (Z_mod_lt y wB wB_pos); omega.
 rewrite Z.mul_1_l, Z.add_comm, Z.add_move_r.
 apply Zmod_small;
  generalize (Z_mod_lt x wB wB_pos) (Z_mod_lt y wB wB_pos); omega.
 Qed.

 Lemma spec_add_carry_c : forall x y, [+|add_carry_c x y|] = [|x|] + [|y|] + 1.
 Proof.
 intros; unfold add_carry_c, to_Z, interp_carry.
 destruct Z_lt_le_dec.
 apply Zmod_small;
  generalize (Z_mod_lt x wB wB_pos) (Z_mod_lt y wB wB_pos); omega.
 rewrite Z.mul_1_l, Z.add_comm, Z.add_move_r.
 apply Zmod_small;
  generalize (Z_mod_lt x wB wB_pos) (Z_mod_lt y wB wB_pos); omega.
 Qed.

 Lemma spec_succ : forall x, [|succ x|] = ([|x|] + 1) mod wB.
 Proof.
 intros; unfold succ, to_Z, Z.succ.
 symmetry; apply Zplus_mod_idemp_l.
 Qed.

 Lemma spec_add : forall x y, [|add x y|] = ([|x|] + [|y|]) mod wB.
 Proof.
 intros; unfold add, to_Z; apply Zplus_mod.
 Qed.

 Lemma spec_add_carry :
	 forall x y, [|add_carry x y|] = ([|x|] + [|y|] + 1) mod wB.
 Proof.
 intros; unfold add_carry, to_Z.
 rewrite <- Zplus_mod_idemp_l.
 rewrite (Zplus_mod x y).
 rewrite Zplus_mod_idemp_l; auto.
 Qed.

 Definition pred_c x :=
  if eq0 x then C1 (wB-1) else C0 (x-1).

 Definition sub_c x y :=
  let z := [|x|]-[|y|] in
  if Z_lt_le_dec z 0 then C1 (wB+z) else C0 z.

 Definition sub_carry_c x y :=
  let z := [|x|]-[|y|]-1 in
  if Z_lt_le_dec z 0 then C1 (wB+z) else C0 z.

 Definition pred := Z.pred.
 Definition sub := Z.sub.
 Definition sub_carry x y := x - y - 1.

 Lemma spec_pred_c : forall x, [-|pred_c x|] = [|x|] - 1.
 Proof.
 intros; unfold pred_c, to_Z, interp_carry.
 case_eq (eq0 x); intros.
 fold [|x|]; rewrite spec_eq0; auto.
 replace ((wB-1) mod wB) with (wB-1); auto with zarith.
 symmetry; apply Zmod_small; generalize wB_pos; omega.

 assert (x mod wB <> 0).
  unfold eq0, to_Z in *; now destruct (x mod wB).
 rewrite <- Zminus_mod_idemp_l.
 apply Zmod_small.
 generalize (Z_mod_lt x wB wB_pos); omega.
 Qed.

 Lemma spec_sub_c : forall x y, [-|sub_c x y|] = [|x|] - [|y|].
 Proof.
 intros; unfold sub_c, to_Z, interp_carry.
 destruct Z_lt_le_dec.
 replace ((wB + (x mod wB - y mod wB)) mod wB) with
   (wB + (x mod wB - y mod wB)).
 omega.
 symmetry; apply Zmod_small.
 generalize wB_pos (Z_mod_lt x wB wB_pos) (Z_mod_lt y wB wB_pos); omega.

 apply Zmod_small.
 generalize wB_pos (Z_mod_lt x wB wB_pos) (Z_mod_lt y wB wB_pos); omega.
 Qed.

 Lemma spec_sub_carry_c : forall x y, [-|sub_carry_c x y|] = [|x|] - [|y|] - 1.
 Proof.
 intros; unfold sub_carry_c, to_Z, interp_carry.
 destruct Z_lt_le_dec.
 replace ((wB + (x mod wB - y mod wB - 1)) mod wB) with
   (wB + (x mod wB - y mod wB -1)).
 omega.
 symmetry; apply Zmod_small.
 generalize wB_pos (Z_mod_lt x wB wB_pos) (Z_mod_lt y wB wB_pos); omega.

 apply Zmod_small.
 generalize wB_pos (Z_mod_lt x wB wB_pos) (Z_mod_lt y wB wB_pos); omega.
 Qed.

 Lemma spec_pred : forall x, [|pred x|] = ([|x|] - 1) mod wB.
 Proof.
 intros; unfold pred, to_Z, Z.pred.
 rewrite <- Zplus_mod_idemp_l; auto.
 Qed.

 Lemma spec_sub : forall x y, [|sub x y|] = ([|x|] - [|y|]) mod wB.
 Proof.
 intros; unfold sub, to_Z; apply Zminus_mod.
 Qed.

 Lemma spec_sub_carry :
  forall x y, [|sub_carry x y|] = ([|x|] - [|y|] - 1) mod wB.
 Proof.
 intros; unfold sub_carry, to_Z.
 rewrite <- Zminus_mod_idemp_l.
 rewrite (Zminus_mod x y).
 rewrite Zminus_mod_idemp_l.
 auto.
 Qed.

 Definition mul_c x y :=
  let (h,l) := Z.div_eucl ([|x|]*[|y|]) wB in
  if eq0 h then if eq0 l then W0 else WW h l else WW h l.

 Definition mul := Z.mul.

 Definition square_c x := mul_c x x.

 Lemma spec_mul_c : forall x y, [|| mul_c x y ||] = [|x|] * [|y|].
 Proof.
 intros; unfold mul_c, zn2z_to_Z.
 assert (Z.div_eucl ([|x|]*[|y|]) wB = (([|x|]*[|y|])/wB,([|x|]*[|y|]) mod wB)).
  unfold Z.modulo, Z.div; destruct Z.div_eucl; auto.
 generalize (Z_div_mod ([|x|]*[|y|]) wB wB_pos); destruct Z.div_eucl as (h,l).
 destruct 1; injection H as ? ?.
 rewrite H0.
 assert ([|l|] = l).
  apply Zmod_small; auto.
 assert ([|h|] = h).
  apply Zmod_small.
  subst h.
  split.
  apply Z_div_pos; auto with zarith.
  apply Zdiv_lt_upper_bound; auto with zarith.
  apply Z.mul_lt_mono_nonneg; auto with zarith.
 clear H H0 H1 H2.
 case_eq (eq0 h); simpl; intros.
 case_eq (eq0 l); simpl; intros.
 rewrite <- H3, <- H4, (spec_eq0 h), (spec_eq0 l); auto with zarith.
 rewrite H3, H4; auto with zarith.
 rewrite H3, H4; auto with zarith.
 Qed.

 Lemma spec_mul : forall x y, [|mul x y|] = ([|x|] * [|y|]) mod wB.
 Proof.
 intros; unfold mul, to_Z; apply Zmult_mod.
 Qed.

 Lemma spec_square_c : forall x, [|| square_c x||] = [|x|] * [|x|].
 Proof.
 intros x; exact (spec_mul_c x x).
 Qed.

 Definition div x y := Z.div_eucl [|x|] [|y|].

 Lemma spec_div : forall a b, 0 < [|b|] ->
      let (q,r) := div a b in
      [|a|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|].
 Proof.
 intros; unfold div.
 assert ([|b|]>0) by auto with zarith.
 assert (Z.div_eucl [|a|] [|b|] = ([|a|]/[|b|], [|a|] mod [|b|])).
  unfold Z.modulo, Z.div; destruct Z.div_eucl; auto.
 generalize (Z_div_mod [|a|] [|b|] H0).
 destruct Z.div_eucl as (q,r); destruct 1; intros.
 injection H1 as ? ?.
 assert ([|r|]=r).
  apply Zmod_small; generalize (Z_mod_lt b wB wB_pos); fold [|b|];
   auto with zarith.
 assert ([|q|]=q).
  apply Zmod_small.
  subst q.
  split.
  apply Z_div_pos; auto with zarith.
  apply Zdiv_lt_upper_bound; auto with zarith.
  apply Z.lt_le_trans with (wB*1).
  rewrite Z.mul_1_r; auto with zarith.
  apply Z.mul_le_mono_nonneg; generalize wB_pos; auto with zarith.
 rewrite H5, H6; rewrite Z.mul_comm; auto with zarith.
 Qed.

 Definition div_gt := div.

 Lemma spec_div_gt : forall a b, [|a|] > [|b|] -> 0 < [|b|] ->
      let (q,r) := div_gt a b in
      [|a|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|].
 Proof.
 intros.
 apply spec_div; auto.
 Qed.

 Definition modulo x y := [|x|] mod [|y|].
 Definition modulo_gt x y := [|x|] mod [|y|].

 Lemma spec_modulo :  forall a b, 0 < [|b|] ->
      [|modulo a b|] = [|a|] mod [|b|].
 Proof.
 intros; unfold modulo.
 apply Zmod_small.
 assert ([|b|]>0) by auto with zarith.
 generalize (Z_mod_lt [|a|] [|b|] H0) (Z_mod_lt b wB wB_pos).
 fold [|b|]; omega.
 Qed.

 Lemma spec_modulo_gt : forall a b, [|a|] > [|b|] -> 0 < [|b|] ->
      [|modulo_gt a b|] = [|a|] mod [|b|].
 Proof.
 intros; apply spec_modulo; auto.
 Qed.

 Definition gcd x y := Z.gcd [|x|] [|y|].
 Definition gcd_gt x y := Z.gcd [|x|] [|y|].

 Lemma Zgcd_bound : forall a b, 0<=a -> 0<=b -> Z.gcd a b <= Z.max a b.
 Proof.
 intros.
 generalize (Zgcd_is_gcd a b); inversion_clear 1.
 destruct H2 as (q,H2); destruct H3 as (q',H3); clear H4.
 assert (H4:=Z.gcd_nonneg a b).
 destruct (Z.eq_dec (Z.gcd a b) 0) as [->|Hneq].
 generalize (Zmax_spec a b); omega.
 assert (0 <= q).
  apply Z.mul_le_mono_pos_r with (Z.gcd a b); auto with zarith.
 destruct (Z.eq_dec q 0).

 subst q; simpl in *; subst a; simpl; auto.
 generalize (Zmax_spec 0 b) (Zabs_spec b); omega.

 apply Z.le_trans with a.
 rewrite H2 at 2.
 rewrite <- (Z.mul_1_l (Z.gcd a b)) at 1.
 apply Z.mul_le_mono_nonneg; auto with zarith.
 generalize (Zmax_spec a b); omega.
 Qed.

 Lemma spec_gcd : forall a b, Zis_gcd [|a|] [|b|] [|gcd a b|].
 Proof.
 intros; unfold gcd.
 generalize (Z_mod_lt a wB wB_pos)(Z_mod_lt b wB wB_pos); intros.
 fold [|a|] in *; fold [|b|] in *.
 replace ([|Z.gcd [|a|] [|b|]|]) with (Z.gcd [|a|] [|b|]).
 apply Zgcd_is_gcd.
 symmetry; apply Zmod_small.
 split.
 apply Z.gcd_nonneg.
 apply Z.le_lt_trans with (Z.max [|a|] [|b|]).
 apply Zgcd_bound; auto with zarith.
 generalize (Zmax_spec [|a|] [|b|]); omega.
 Qed.

 Lemma spec_gcd_gt : forall a b, [|a|] > [|b|] ->
      Zis_gcd [|a|] [|b|] [|gcd_gt a b|].
 Proof.
  intros. apply spec_gcd; auto.
 Qed.

 Definition div21 a1 a2 b :=
  Z.div_eucl ([|a1|]*wB+[|a2|]) [|b|].

 Lemma spec_div21 : forall a1 a2 b,
      wB/2 <= [|b|] ->
      [|a1|] < [|b|] ->
      let (q,r) := div21 a1 a2 b in
      [|a1|] *wB+ [|a2|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|].
 Proof.
 intros; unfold div21.
 generalize (Z_mod_lt a1 wB wB_pos); fold [|a1|]; intros.
 generalize (Z_mod_lt a2 wB wB_pos); fold [|a2|]; intros.
 assert ([|b|]>0) by auto with zarith.
 remember ([|a1|]*wB+[|a2|]) as a.
 assert (Z.div_eucl a [|b|] = (a/[|b|], a mod [|b|])).
  unfold Z.modulo, Z.div; destruct Z.div_eucl; auto.
 generalize (Z_div_mod a [|b|] H3).
 destruct Z.div_eucl as (q,r); destruct 1; intros.
 injection H4 as ? ?.
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
  apply Z.lt_le_trans with ([|a1|]*wB+wB); auto with zarith.
 rewrite H8, H9; rewrite Z.mul_comm; auto with zarith.
 Qed.

 Definition add_mul_div p x y :=
   ([|x|] * (2 ^ [|p|]) + [|y|] / (2 ^ ((Zpos digits) - [|p|]))).
 Lemma spec_add_mul_div : forall x y p,
       [|p|] <= Zpos digits ->
       [| add_mul_div p x y |] =
         ([|x|] * (2 ^ [|p|]) +
          [|y|] / (2 ^ ((Zpos digits) - [|p|]))) mod wB.
 Proof.
 intros; unfold add_mul_div; auto.
 Qed.

 Definition pos_mod p w := [|w|] mod (2 ^ [|p|]).
 Lemma spec_pos_mod : forall w p,
       [|pos_mod p w|] = [|w|] mod (2 ^ [|p|]).
 Proof.
 intros; unfold pos_mod.
 apply Zmod_small.
 generalize (Z_mod_lt [|w|] (2 ^ [|p|])); intros.
 split.
 destruct H; auto using Z.lt_gt with zarith.
 apply Z.le_lt_trans with [|w|]; auto with zarith.
 apply Zmod_le; auto with zarith.
 Qed.

 Definition is_even x :=
   if Z.eq_dec ([|x|] mod 2) 0 then true else false.

 Lemma spec_is_even : forall x,
      if is_even x then [|x|] mod 2 = 0 else [|x|] mod 2 = 1.
 Proof.
 intros; unfold is_even; destruct Z.eq_dec; auto.
 generalize (Z_mod_lt [|x|] 2); omega.
 Qed.

 Definition sqrt x := Z.sqrt [|x|].
 Lemma spec_sqrt : forall x,
       [|sqrt x|] ^ 2 <= [|x|] < ([|sqrt x|] + 1) ^ 2.
 Proof.
 intros.
 unfold sqrt.
 repeat rewrite Z.pow_2_r.
 replace [|Z.sqrt [|x|]|] with (Z.sqrt [|x|]).
 apply Z.sqrt_spec; auto with zarith.
 symmetry; apply Zmod_small.
 split. apply Z.sqrt_nonneg; auto.
 apply Z.le_lt_trans with [|x|]; auto.
 apply Z.sqrt_le_lin; auto.
 Qed.

 Definition sqrt2 x y :=
  let z := [|x|]*wB+[|y|] in
  match z with
   | Z0 => (0, C0 0)
   | Zpos p =>
      let (s,r) := Z.sqrtrem (Zpos p) in
      (s, if Z_lt_le_dec r wB then C0 r else C1 (r-wB))
   | Zneg _ => (0, C0 0)
  end.

 Lemma spec_sqrt2 : forall x y,
       wB/ 4 <= [|x|] ->
       let (s,r) := sqrt2 x y in
          [||WW x y||] = [|s|] ^ 2 + [+|r|] /\
          [+|r|] <= 2 * [|s|].
 Proof.
 intros; unfold sqrt2.
 simpl zn2z_to_Z.
 remember ([|x|]*wB+[|y|]) as z.
 destruct z.
 auto with zarith.
 generalize (Z.sqrtrem_spec (Zpos p)).
 destruct Z.sqrtrem as (s,r); intros [U V]; auto with zarith.
 assert (s < wB).
  destruct (Z_lt_le_dec s wB); auto.
  assert (wB * wB <= Zpos p).
   rewrite U.
   apply Z.le_trans with (s*s); try omega.
   apply Z.mul_le_mono_nonneg; generalize wB_pos; auto with zarith.
  assert (Zpos p < wB*wB).
   rewrite Heqz.
   replace (wB*wB) with ((wB-1)*wB+wB) by ring.
   apply Z.add_le_lt_mono; auto with zarith.
   apply Z.mul_le_mono_nonneg; auto with zarith.
   generalize (spec_to_Z x); auto with zarith.
   generalize wB_pos; auto with zarith.
  omega.
 replace [|s|] with s by (symmetry; apply Zmod_small; auto with zarith).
 destruct Z_lt_le_dec; unfold interp_carry.
 replace [|r|] with r by (symmetry; apply Zmod_small; auto with zarith).
 rewrite Z.pow_2_r; auto with zarith.
 replace [|r-wB|] with (r-wB) by (symmetry; apply Zmod_small; auto with zarith).
 rewrite Z.pow_2_r; omega.

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

 Definition head0 x := match [|x|] with
   | Z0 => zdigits
   | Zpos p => zdigits - log_inf p - 1
   | _ => 0
  end.

 Lemma spec_head00:  forall x, [|x|] = 0 -> [|head0 x|] = Zpos digits.
 Proof.
  unfold head0; intros.
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
 replace p with (Z.succ (p-1)) in H; auto with zarith.
 rewrite Z.pow_succ_r in H; auto with zarith.

 assert (0 < p) by (destruct p; compute; auto with zarith; discriminate).
 cut (log_inf x < p - 1); [omega| ].
 apply IHx.
 change (Zpos x~0) with (2*(Zpos x)) in H.
 replace p with (Z.succ (p-1)) in H; auto with zarith.
 rewrite Z.pow_succ_r in H; auto with zarith.

 simpl; intros; destruct p; compute; auto with zarith.
 Qed.


 Lemma spec_head0  : forall x,  0 < [|x|] ->
	 wB/ 2 <= 2 ^ ([|head0 x|]) * [|x|] < wB.
 Proof.
 intros; unfold head0.
 generalize (spec_to_Z x).
 destruct [|x|]; try discriminate.
 intros.
 destruct (log_inf_correct p).
 rewrite 2 two_p_power2 in H2; auto with zarith.
 assert (0 <= zdigits - log_inf p - 1 < wB).
  split.
  cut (log_inf p < zdigits); try omega.
  unfold zdigits.
  unfold wB, base in *.
  apply log_inf_bounded; auto with zarith.
  apply Z.lt_trans with zdigits.
  omega.
  unfold zdigits, wB, base; apply Zpower2_lt_lin; auto with zarith.

 unfold to_Z; rewrite (Zmod_small _ _ H3).
 destruct H2.
 split.
 apply Z.le_trans with (2^(zdigits - log_inf p - 1)*(2^log_inf p)).
 apply Zdiv_le_upper_bound; auto with zarith.
 rewrite <- Zpower_exp; auto with zarith.
 rewrite Z.mul_comm; rewrite <- Z.pow_succ_r; auto with zarith.
 replace (Z.succ (zdigits - log_inf p -1 +log_inf p)) with zdigits
   by ring.
 unfold wB, base, zdigits; auto with zarith.
 apply Z.mul_le_mono_nonneg; auto with zarith.

 apply Z.lt_le_trans
   with (2^(zdigits - log_inf p - 1)*(2^(Z.succ (log_inf p)))).
 apply Z.mul_lt_mono_pos_l; auto with zarith.
 rewrite <- Zpower_exp; auto with zarith.
 replace (zdigits - log_inf p -1 +Z.succ (log_inf p)) with zdigits
   by ring.
 unfold wB, base, zdigits; auto with zarith.
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
 assert (Z.succ (Zpos (Pos.pred d)) = Zpos d).
  simpl; f_equal.
  rewrite Pos.add_1_r.
  destruct (Pos.succ_pred_or d); auto.
  rewrite H1 in H0; elim H0; auto.
 assert (Ptail p < Zpos (Pos.pred d)).
  apply IHp.
  apply Z.mul_lt_mono_pos_r with 2; auto with zarith.
  rewrite (Z.mul_comm (Zpos p)).
  change (2 * Zpos p) with (Zpos p~0).
  rewrite Z.mul_comm.
  rewrite <- Z.pow_succ_r; auto with zarith.
  rewrite H1; auto.
 rewrite <- H1; omega.
 Qed.

 Definition tail0 x :=
  match [|x|] with
   | Z0 => zdigits
   | Zpos p => Ptail p
   | Zneg _ => 0
  end.

 Lemma spec_tail00:  forall x, [|x|] = 0 -> [|tail0 x|] = Zpos digits.
 Proof.
  unfold tail0; intros.
  rewrite H; simpl.
  apply spec_zdigits.
 Qed.

 Lemma spec_tail0  : forall x, 0 < [|x|] ->
         exists y, 0 <= y /\ [|x|] = (2 * y + 1) * (2 ^ [|tail0 x|]).
 Proof.
 intros; unfold tail0.
 generalize (spec_to_Z x).
 destruct [|x|]; try discriminate; intros.
 assert ([|Ptail p|] = Ptail p).
  apply Zmod_small.
  split; auto.
  unfold wB, base in *.
  apply Z.lt_trans with (Zpos digits).
  apply Ptail_bounded; auto with zarith.
  apply Zpower2_lt_lin; auto with zarith.
 rewrite H1.

 clear; induction p.
 exists (Zpos p); simpl; rewrite Pos.mul_1_r; auto with zarith.
 destruct IHp as (y & Yp & Ye).
 exists y.
 split; auto.
 change (Zpos p~0) with (2*Zpos p).
 rewrite Ye.
 change (Ptail p~0) with (Z.succ (Ptail p)).
 rewrite Z.pow_succ_r; auto; ring.

 exists 0; simpl; auto with zarith.
 Qed.

 Definition lor := Z.lor.
 Definition land := Z.land.
 Definition lxor := Z.lxor.

 Lemma spec_lor x y : [|lor x y|] = Z.lor [|x|] [|y|].
 Proof.
 unfold lor, to_Z.
 apply Z.bits_inj'; intros n Hn. rewrite Z.lor_spec.
 unfold wB, base.
 destruct (Z.le_gt_cases (Z.pos digits) n).
 - rewrite !Z.mod_pow2_bits_high; auto with zarith.
 - rewrite !Z.mod_pow2_bits_low, Z.lor_spec; auto with zarith.
 Qed.

 Lemma spec_land x y : [|land x y|] = Z.land [|x|] [|y|].
 Proof.
 unfold land, to_Z.
 apply Z.bits_inj'; intros n Hn. rewrite Z.land_spec.
 unfold wB, base.
 destruct (Z.le_gt_cases (Z.pos digits) n).
 - rewrite !Z.mod_pow2_bits_high; auto with zarith.
 - rewrite !Z.mod_pow2_bits_low, Z.land_spec; auto with zarith.
 Qed.

 Lemma spec_lxor x y : [|lxor x y|] = Z.lxor [|x|] [|y|].
 Proof.
 unfold lxor, to_Z.
 apply Z.bits_inj'; intros n Hn. rewrite Z.lxor_spec.
 unfold wB, base.
 destruct (Z.le_gt_cases (Z.pos digits) n).
 - rewrite !Z.mod_pow2_bits_high; auto with zarith.
 - rewrite !Z.mod_pow2_bits_low, Z.lxor_spec; auto with zarith.
 Qed.

 (** Let's now group everything in two records *)

 Instance zmod_ops : ZnZ.Ops Z := ZnZ.MkOps
    (digits : positive)
    (zdigits: t)
    (to_Z   : t -> Z)
    (of_pos : positive -> N * t)
    (head0  : t -> t)
    (tail0  : t -> t)

    (zero   : t)
    (one    : t)
    (minus_one : t)

    (compare     : t -> t -> comparison)
    (eq0         : t -> bool)

    (opp_c       : t -> carry t)
    (opp         : t -> t)
    (opp_carry   : t -> t)

    (succ_c      : t -> carry t)
    (add_c       : t -> t -> carry t)
    (add_carry_c : t -> t -> carry t)
    (succ        : t -> t)
    (add         : t -> t -> t)
    (add_carry   : t -> t -> t)

    (pred_c      : t -> carry t)
    (sub_c       : t -> t -> carry t)
    (sub_carry_c : t -> t -> carry t)
    (pred        : t -> t)
    (sub         : t -> t -> t)
    (sub_carry   : t -> t -> t)

    (mul_c       : t -> t -> zn2z t)
    (mul         : t -> t -> t)
    (square_c    : t -> zn2z t)

    (div21       : t -> t -> t -> t*t)
    (div_gt      : t -> t -> t * t)
    (div         : t -> t -> t * t)

    (modulo_gt      : t -> t -> t)
    (modulo         : t -> t -> t)

    (gcd_gt      : t -> t -> t)
    (gcd         : t -> t -> t)
    (add_mul_div : t -> t -> t -> t)
    (pos_mod     : t -> t -> t)

    (is_even     : t -> bool)
    (sqrt2       : t -> t -> t * carry t)
    (sqrt        : t -> t)
    (lor         : t -> t -> t)
    (land         : t -> t -> t)
    (lxor         : t -> t -> t).

 Instance zmod_specs : ZnZ.Specs zmod_ops := ZnZ.MkSpecs
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

    spec_modulo_gt
    spec_modulo

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
    spec_sqrt
    spec_lor
    spec_land
    spec_lxor.

End ZModulo.

(** A modular version of the previous construction. *)

Module Type PositiveNotOne.
 Parameter p : positive.
 Axiom not_one : p <> 1%positive.
End PositiveNotOne.

Module ZModuloCyclicType (P:PositiveNotOne) <: CyclicType.
 Definition t := Z.
 Instance ops : ZnZ.Ops t := zmod_ops P.p.
 Instance specs : ZnZ.Specs ops := zmod_specs P.not_one.
End ZModuloCyclicType.
