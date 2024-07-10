(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Type [Z] viewed modulo [2^d] implements CyclicAxioms. *)

(** This library has been deprecated since Coq version 8.17. *)
Local Set Warnings "-deprecated".

(** Even if the construction provided here is not reused for building
  the efficient arbitrary precision numbers, it provides a simple
  implementation of CyclicAxioms, hence ensuring its coherence. *)

Set Implicit Arguments.

From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Zpow_facts.
From Stdlib Require Import DoubleType.
From Stdlib Require Import CyclicAxioms.
From Stdlib Require Import Lia.

Local Open Scope Z_scope.

Section ZModulo.

 Variable digits : positive.
 Hypothesis digits_ne_1 : digits <> 1%positive.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition wB := base digits.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition t := Z.
 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition zdigits := Zpos digits.
 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition to_Z x := x mod wB.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Notation "[| x |]" := (to_Z x)  (at level 0, x at level 99).

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Notation "[+| c |]" :=
   (interp_carry 1 wB to_Z c)  (at level 0, c at level 99).

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Notation "[-| c |]" :=
   (interp_carry (-1) wB to_Z c)  (at level 0, c at level 99).

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Notation "[|| x ||]" :=
   (zn2z_to_Z wB to_Z x)  (at level 0, x at level 99).

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_more_than_1_digit: 1 < Zpos digits.
 Proof.
  generalize digits_ne_1; destruct digits; red; auto.
  destruct 1; auto.
 Qed.
 Let digits_gt_1 := spec_more_than_1_digit.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma wB_pos : wB > 0.
 Proof.
  apply Z.lt_gt.
  unfold wB, base; auto with zarith.
 Qed.
 #[local]
 Hint Resolve wB_pos : core.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_to_Z_1 : forall x, 0 <= [|x|].
 Proof.
  unfold to_Z; intros; destruct (Z_mod_lt x wB wB_pos); auto.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_to_Z_2 : forall x, [|x|] < wB.
 Proof.
  unfold to_Z; intros; destruct (Z_mod_lt x wB wB_pos); auto.
 Qed.
 #[local]
 Hint Resolve spec_to_Z_1 spec_to_Z_2 : core.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_to_Z : forall x, 0 <= [|x|] < wB.
 Proof.
  auto.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition of_pos x :=
   let (q,r) := Z.pos_div_eucl x wB in (N_of_Z q, r).

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_of_pos : forall p,
   Zpos p = (Z.of_N (fst (of_pos p)))*wB + [|(snd (of_pos p))|].
 Proof.
  intros; unfold of_pos; simpl.
  generalize (Z_div_mod_POS wB wB_pos p).
  destruct (Z.pos_div_eucl p wB); simpl; destruct 1.
  unfold to_Z; rewrite Zmod_small; auto.
  assert (0 <= z). {
   replace z with (Zpos p / wB) by
    (symmetry; apply Zdiv_unique with z0; auto).
   apply Z_div_pos; auto with zarith.
  }
  replace (Z.of_N (N_of_Z z)) with z by
    (destruct z; simpl; auto; elim H1; auto).
  rewrite Z.mul_comm; auto.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_zdigits : [|zdigits|] = Zpos digits.
 Proof.
  unfold to_Z, zdigits.
  apply Zmod_small.
  unfold wB, base.
  split; auto with zarith.
  apply Zpower2_lt_lin; auto with zarith.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition zero := 0.
 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition one := 1.
 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition minus_one := wB - 1.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_0 : [|zero|] = 0.
 Proof.
  unfold to_Z, zero.
  apply Zmod_small; generalize wB_pos. lia.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_1 : [|one|] = 1.
 Proof.
  unfold to_Z, one.
  apply Zmod_small; split; auto with zarith.
  unfold wB, base.
  apply Z.lt_trans with (Zpos digits); auto.
  apply Zpower2_lt_lin; auto with zarith.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_Bm1 : [|minus_one|] = wB - 1.
 Proof.
  unfold to_Z, minus_one.
  apply Zmod_small; split. 2: lia.
  unfold wB, base.
  cut (1 <= 2 ^ Zpos digits). { lia. }
  apply Z.le_trans with (Zpos digits). { lia. }
  apply Zpower2_le_lin; auto with zarith.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition compare x y := Z.compare [|x|] [|y|].

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_compare : forall x y,
   compare x y = Z.compare [|x|] [|y|].
 Proof. reflexivity. Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition eq0 x :=
   match [|x|] with Z0 => true | _ => false end.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_eq0 : forall x, eq0 x = true -> [|x|] = 0.
 Proof.
  unfold eq0; intros; now destruct [|x|].
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition opp_c x :=
   if eq0 x then C0 0 else C1 (- x).
 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition opp x := - x.
 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition opp_carry x := - x - 1.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_opp_c : forall x, [-|opp_c x|] = -[|x|].
 Proof.
 intros; unfold opp_c, to_Z; auto.
 case_eq (eq0 x); intros; unfold interp_carry.
 - fold [|x|]; rewrite (spec_eq0 x H); auto.
 - assert (x mod wB <> 0).
   { unfold eq0, to_Z in H.
     intro H0; rewrite H0 in H; discriminate. }
   rewrite Z_mod_nz_opp_full; lia.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_opp : forall x, [|opp x|] = (-[|x|]) mod wB.
 Proof.
 intros; unfold opp, to_Z; auto.
 change ((- x) mod wB = (0 - (x mod wB)) mod wB).
 rewrite Zminus_mod_idemp_r; simpl; auto.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_opp_carry : forall x, [|opp_carry x|] = wB - [|x|] - 1.
 Proof.
 intros; unfold opp_carry, to_Z; auto.
 replace (- x - 1) with (- 1 - x) by lia.
 rewrite <- Zminus_mod_idemp_r.
 replace ( -1 - x mod wB) with (0 + ( -1 - x mod wB)) by lia.
 rewrite <- (Z_mod_same_full wB).
 rewrite Zplus_mod_idemp_l.
 replace (wB + (-1 - x mod wB)) with (wB - x mod wB -1) by lia.
 apply Zmod_small.
 generalize (Z_mod_lt x wB wB_pos); lia.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition succ_c x :=
  let y := Z.succ x in
  if eq0 y then C1 0 else C0 y.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition add_c x y :=
  let z := [|x|] + [|y|] in
  if Z_lt_le_dec z wB then C0 z else C1 (z-wB).

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition add_carry_c x y :=
  let z := [|x|]+[|y|]+1 in
  if Z_lt_le_dec z wB then C0 z else C1 (z-wB).

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition succ := Z.succ.
 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition add := Z.add.
 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition add_carry x y := x + y + 1.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma Zmod_equal :
  forall x y z, z>0 -> (x-y) mod z = 0 -> x mod z = y mod z.
 Proof.
 intros.
 generalize (Z_div_mod_eq_full (x-y) z); rewrite H0, Z.add_0_r.
 remember ((x-y)/z) as k.
 rewrite Z.sub_move_r, Z.add_comm, Z.mul_comm. intros ->.
 now apply Z_mod_plus.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_succ_c : forall x, [+|succ_c x|] = [|x|] + 1.
 Proof.
 intros; unfold succ_c, to_Z, Z.succ.
 case_eq (eq0 (x+1)); intros; unfold interp_carry.

 - rewrite Z.mul_1_l.
   replace (wB + 0 mod wB) with wB by auto with zarith.
   symmetry. rewrite Z.add_move_r.
   assert ((x+1) mod wB = 0) by (apply spec_eq0; auto).
   replace (wB-1) with ((wB-1) mod wB) by
     (apply Zmod_small; generalize wB_pos; lia).
   rewrite <- Zminus_mod_idemp_l; rewrite Z_mod_same; simpl; auto.
   apply Zmod_equal; auto.

 - assert ((x+1) mod wB <> 0). {
     unfold eq0, to_Z in *; now destruct ((x+1) mod wB).
   }
   assert (x mod wB + 1 <> wB). {
     contradict H0.
     rewrite Z.add_move_r in H0; simpl in H0.
     rewrite <- Zplus_mod_idemp_l; rewrite H0.
     replace (wB-1+1) with wB by lia; apply Z_mod_same; auto.
   }
   rewrite <- Zplus_mod_idemp_l.
   apply Zmod_small.
   generalize (Z_mod_lt x wB wB_pos); lia.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_add_c : forall x y, [+|add_c x y|] = [|x|] + [|y|].
 Proof.
 intros; unfold add_c, to_Z, interp_carry.
 destruct Z_lt_le_dec.
 - apply Zmod_small;
     generalize (Z_mod_lt x wB wB_pos) (Z_mod_lt y wB wB_pos); lia.
 - rewrite Z.mul_1_l, Z.add_comm, Z.add_move_r.
   apply Zmod_small;
     generalize (Z_mod_lt x wB wB_pos) (Z_mod_lt y wB wB_pos); lia.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_add_carry_c : forall x y, [+|add_carry_c x y|] = [|x|] + [|y|] + 1.
 Proof.
 intros; unfold add_carry_c, to_Z, interp_carry.
 destruct Z_lt_le_dec.
 - apply Zmod_small;
     generalize (Z_mod_lt x wB wB_pos) (Z_mod_lt y wB wB_pos); lia.
 - rewrite Z.mul_1_l, Z.add_comm, Z.add_move_r.
   apply Zmod_small;
     generalize (Z_mod_lt x wB wB_pos) (Z_mod_lt y wB wB_pos); lia.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_succ : forall x, [|succ x|] = ([|x|] + 1) mod wB.
 Proof.
 intros; unfold succ, to_Z, Z.succ.
 symmetry; apply Zplus_mod_idemp_l.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_add : forall x y, [|add x y|] = ([|x|] + [|y|]) mod wB.
 Proof.
 intros; unfold add, to_Z; apply Zplus_mod.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_add_carry :
         forall x y, [|add_carry x y|] = ([|x|] + [|y|] + 1) mod wB.
 Proof.
 intros; unfold add_carry, to_Z.
 rewrite <- Zplus_mod_idemp_l.
 rewrite (Zplus_mod x y).
 rewrite Zplus_mod_idemp_l; auto.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition pred_c x :=
  if eq0 x then C1 (wB-1) else C0 (x-1).

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition sub_c x y :=
  let z := [|x|]-[|y|] in
  if Z_lt_le_dec z 0 then C1 (wB+z) else C0 z.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition sub_carry_c x y :=
  let z := [|x|]-[|y|]-1 in
  if Z_lt_le_dec z 0 then C1 (wB+z) else C0 z.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition pred := Z.pred.
 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition sub := Z.sub.
 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition sub_carry x y := x - y - 1.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_pred_c : forall x, [-|pred_c x|] = [|x|] - 1.
 Proof.
 intros; unfold pred_c, to_Z, interp_carry.
 case_eq (eq0 x); intros.
 - fold [|x|]; rewrite spec_eq0; auto.
   replace ((wB-1) mod wB) with (wB-1).
   + lia.
   + symmetry; apply Zmod_small; generalize wB_pos; lia.

 - assert (x mod wB <> 0).
   + unfold eq0, to_Z in *; now destruct (x mod wB).
   + rewrite <- Zminus_mod_idemp_l.
     apply Zmod_small.
     generalize (Z_mod_lt x wB wB_pos); lia.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_sub_c : forall x y, [-|sub_c x y|] = [|x|] - [|y|].
 Proof.
 intros; unfold sub_c, to_Z, interp_carry.
 destruct Z_lt_le_dec.
 - replace ((wB + (x mod wB - y mod wB)) mod wB) with
     (wB + (x mod wB - y mod wB)).
   + lia.
   + symmetry; apply Zmod_small.
     generalize wB_pos (Z_mod_lt x wB wB_pos) (Z_mod_lt y wB wB_pos); lia.

 - apply Zmod_small.
   generalize wB_pos (Z_mod_lt x wB wB_pos) (Z_mod_lt y wB wB_pos); lia.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_sub_carry_c : forall x y, [-|sub_carry_c x y|] = [|x|] - [|y|] - 1.
 Proof.
 intros; unfold sub_carry_c, to_Z, interp_carry.
 destruct Z_lt_le_dec.
 - replace ((wB + (x mod wB - y mod wB - 1)) mod wB) with
     (wB + (x mod wB - y mod wB -1)).
   + lia.
   + symmetry; apply Zmod_small.
     generalize wB_pos (Z_mod_lt x wB wB_pos) (Z_mod_lt y wB wB_pos); lia.

 - apply Zmod_small.
   generalize wB_pos (Z_mod_lt x wB wB_pos) (Z_mod_lt y wB wB_pos); lia.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_pred : forall x, [|pred x|] = ([|x|] - 1) mod wB.
 Proof.
 intros; unfold pred, to_Z, Z.pred.
 rewrite <- Zplus_mod_idemp_l; auto.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_sub : forall x y, [|sub x y|] = ([|x|] - [|y|]) mod wB.
 Proof.
 intros; unfold sub, to_Z; apply Zminus_mod.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_sub_carry :
  forall x y, [|sub_carry x y|] = ([|x|] - [|y|] - 1) mod wB.
 Proof.
 intros; unfold sub_carry, to_Z.
 rewrite <- Zminus_mod_idemp_l.
 rewrite (Zminus_mod x y).
 rewrite Zminus_mod_idemp_l.
 auto.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition mul_c x y :=
  let (h,l) := Z.div_eucl ([|x|]*[|y|]) wB in
  if eq0 h then if eq0 l then W0 else WW h l else WW h l.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition mul := Z.mul.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition square_c x := mul_c x x.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_mul_c : forall x y, [|| mul_c x y ||] = [|x|] * [|y|].
 Proof.
 intros; unfold mul_c, zn2z_to_Z.
 assert (Z.div_eucl ([|x|]*[|y|]) wB = (([|x|]*[|y|])/wB,([|x|]*[|y|]) mod wB)).
 - unfold Z.modulo, Z.div; destruct Z.div_eucl; auto.
 - generalize (Z_div_mod ([|x|]*[|y|]) wB wB_pos); destruct Z.div_eucl as (h,l).
   destruct 1; injection H as [= ? ?].
   rewrite H0.
   assert ([|l|] = l).
   + apply Zmod_small; auto.
   + assert ([|h|] = h).
     * apply Zmod_small.
       subst h.
       split.
       -- apply Z_div_pos; auto with zarith.
       -- apply Zdiv_lt_upper_bound.
          ++ lia.
          ++ apply Z.mul_lt_mono_nonneg; auto with zarith.
     * clear H H0 H1 H2.
       case_eq (eq0 h); simpl; intros.
       -- case_eq (eq0 l); simpl; intros.
          ++ rewrite <- H3, <- H4, (spec_eq0 h), (spec_eq0 l); auto. lia.
          ++ rewrite H3, H4; auto with zarith.
       -- rewrite H3, H4; auto with zarith.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_mul : forall x y, [|mul x y|] = ([|x|] * [|y|]) mod wB.
 Proof.
 intros; unfold mul, to_Z; apply Zmult_mod.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_square_c : forall x, [|| square_c x||] = [|x|] * [|x|].
 Proof.
 intros x; exact (spec_mul_c x x).
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition div x y := Z.div_eucl [|x|] [|y|].

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_div : forall a b, 0 < [|b|] ->
      let (q,r) := div a b in
      [|a|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|].
 Proof.
 intros; unfold div.
 assert ([|b|]>0) by lia.
 assert (Z.div_eucl [|a|] [|b|] = ([|a|]/[|b|], [|a|] mod [|b|])).
 { unfold Z.modulo, Z.div; destruct Z.div_eucl; auto. }
 generalize (Z_div_mod [|a|] [|b|] H0).
 destruct Z.div_eucl as (q,r); destruct 1; intros.
 injection H1 as [= ? ?].
 assert ([|r|]=r). {
   apply Zmod_small; generalize (Z_mod_lt b wB wB_pos); fold [|b|];
   lia.
 }
 assert ([|q|]=q). {
  apply Zmod_small.
  subst q.
  split.
  - apply Z_div_pos; auto with zarith.
  - apply Zdiv_lt_upper_bound; auto with zarith.
    apply Z.lt_le_trans with (wB*1).
    + rewrite Z.mul_1_r; auto with zarith.
    + apply Z.mul_le_mono_nonneg; generalize wB_pos; lia.
 }
 rewrite H5, H6; rewrite Z.mul_comm; auto with zarith.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition div_gt := div.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_div_gt : forall a b, [|a|] > [|b|] -> 0 < [|b|] ->
      let (q,r) := div_gt a b in
      [|a|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|].
 Proof.
 intros.
 apply spec_div; auto.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition modulo x y := [|x|] mod [|y|].
 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition modulo_gt x y := [|x|] mod [|y|].

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_modulo :  forall a b, 0 < [|b|] ->
      [|modulo a b|] = [|a|] mod [|b|].
 Proof.
 intros; unfold modulo.
 apply Zmod_small.
 assert ([|b|]>0) by lia.
 generalize (Z_mod_lt [|a|] [|b|] H0) (Z_mod_lt b wB wB_pos).
 fold [|b|]; lia.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_modulo_gt : forall a b, [|a|] > [|b|] -> 0 < [|b|] ->
      [|modulo_gt a b|] = [|a|] mod [|b|].
 Proof.
 intros; apply spec_modulo; auto.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition gcd x y := Z.gcd [|x|] [|y|].
 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition gcd_gt x y := Z.gcd [|x|] [|y|].

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma Zgcd_bound : forall a b, 0<=a -> 0<=b -> Z.gcd a b <= Z.max a b.
 Proof.
 intros.
 generalize (Zgcd_is_gcd a b); inversion_clear 1.
 destruct H2 as (q,H2); destruct H3 as (q',H3); clear H4.
 assert (H4:=Z.gcd_nonneg a b).
 destruct (Z.eq_dec (Z.gcd a b) 0) as [->|Hneq].
 - generalize (Zmax_spec a b); lia.
 - assert (0 <= q).
   { apply Z.mul_le_mono_pos_r with (Z.gcd a b); lia. }
   destruct (Z.eq_dec q 0).

   + subst q; simpl in *; subst a; simpl; auto.
     generalize (Zmax_spec 0 b) (Zabs_spec b); lia.

   + apply Z.le_trans with a.
     * rewrite H2 at 2.
       rewrite <- (Z.mul_1_l (Z.gcd a b)) at 1.
       apply Z.mul_le_mono_nonneg; lia.
     * generalize (Zmax_spec a b); lia.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_gcd : forall a b, Zis_gcd [|a|] [|b|] [|gcd a b|].
 Proof.
 intros; unfold gcd.
 generalize (Z_mod_lt a wB wB_pos)(Z_mod_lt b wB wB_pos); intros.
 fold [|a|] in *; fold [|b|] in *.
 replace ([|Z.gcd [|a|] [|b|]|]) with (Z.gcd [|a|] [|b|]).
 - apply Zgcd_is_gcd.
 - symmetry; apply Zmod_small.
   split.
   + apply Z.gcd_nonneg.
   + apply Z.le_lt_trans with (Z.max [|a|] [|b|]).
     * apply Zgcd_bound; auto with zarith.
     * generalize (Zmax_spec [|a|] [|b|]); lia.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_gcd_gt : forall a b, [|a|] > [|b|] ->
      Zis_gcd [|a|] [|b|] [|gcd_gt a b|].
 Proof.
  intros. apply spec_gcd; auto.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition div21 a1 a2 b :=
  Z.div_eucl ([|a1|]*wB+[|a2|]) [|b|].

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
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
 assert ([|b|]>0) by lia.
 remember ([|a1|]*wB+[|a2|]) as a.
 assert (Z.div_eucl a [|b|] = (a/[|b|], a mod [|b|])).
 { unfold Z.modulo, Z.div; destruct Z.div_eucl; auto. }
 generalize (Z_div_mod a [|b|] H3).
 destruct Z.div_eucl as (q,r); destruct 1; intros.
 injection H4 as [= ? ?].
 assert ([|r|]=r). {
  apply Zmod_small; generalize (Z_mod_lt b wB wB_pos); fold [|b|];
    lia.
 }
 assert ([|q|]=q). {
  apply Zmod_small.
  subst q.
  split.
  - apply Z_div_pos.
    + lia.
    + subst a. nia.
  - apply Zdiv_lt_upper_bound; nia.
 }
 subst a.
 replace (wB*[|b|]) with (([|b|]-1)*wB + wB) by ring.
 lia.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition add_mul_div p x y :=
   ([|x|] * (2 ^ [|p|]) + [|y|] / (2 ^ ((Zpos digits) - [|p|]))).
 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_add_mul_div : forall x y p,
       [|p|] <= Zpos digits ->
       [| add_mul_div p x y |] =
         ([|x|] * (2 ^ [|p|]) +
          [|y|] / (2 ^ ((Zpos digits) - [|p|]))) mod wB.
 Proof.
 intros; unfold add_mul_div; auto.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition pos_mod p w := [|w|] mod (2 ^ [|p|]).
 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_pos_mod : forall w p,
       [|pos_mod p w|] = [|w|] mod (2 ^ [|p|]).
 Proof.
 intros; unfold pos_mod.
 apply Zmod_small.
 generalize (Z_mod_lt [|w|] (2 ^ [|p|])); intros.
 split.
 - destruct H; auto using Z.lt_gt with zarith.
 - apply Z.le_lt_trans with [|w|]; auto with zarith.
   apply Zmod_le; auto with zarith.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition is_even x :=
   if Z.eq_dec ([|x|] mod 2) 0 then true else false.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_is_even : forall x,
      if is_even x then [|x|] mod 2 = 0 else [|x|] mod 2 = 1.
 Proof.
 intros; unfold is_even; destruct Z.eq_dec; auto.
 generalize (Z_mod_lt [|x|] 2); lia.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition sqrt x := Z.sqrt [|x|].
 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_sqrt : forall x,
       [|sqrt x|] ^ 2 <= [|x|] < ([|sqrt x|] + 1) ^ 2.
 Proof.
 intros.
 unfold sqrt.
 repeat rewrite Z.pow_2_r.
 replace [|Z.sqrt [|x|]|] with (Z.sqrt [|x|]).
 - apply Z.sqrt_spec; auto with zarith.
 - symmetry; apply Zmod_small.
   split.
   + apply Z.sqrt_nonneg; auto.
   + apply Z.le_lt_trans with [|x|]; auto.
     apply Z.sqrt_le_lin; auto.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition sqrt2 x y :=
  let z := [|x|]*wB+[|y|] in
  match z with
   | Z0 => (0, C0 0)
   | Zpos p =>
      let (s,r) := Z.sqrtrem (Zpos p) in
      (s, if Z_lt_le_dec r wB then C0 r else C1 (r-wB))
   | Zneg _ => (0, C0 0)
  end.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
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
 - auto with zarith.
 - generalize (Z.sqrtrem_spec (Zpos p)).
 destruct Z.sqrtrem as (s,r); intros [U V]. { lia. }
 assert (s < wB).
 {
  destruct (Z_lt_le_dec s wB); auto.
  assert (wB * wB <= Zpos p). {
   apply Z.le_trans with (s*s). 2: lia.
   apply Z.mul_le_mono_nonneg; generalize wB_pos; lia.
  }
  assert (Zpos p < wB*wB). {
   rewrite Heqz.
   replace (wB*wB) with ((wB-1)*wB+wB) by ring.
   apply Z.add_le_lt_mono. 2: auto with zarith.
   apply Z.mul_le_mono_nonneg. 1, 3-4: auto with zarith.
   1:generalize wB_pos; lia.
   generalize (spec_to_Z x); lia.
  }
  auto with zarith.
 }
 replace [|s|] with s by (symmetry; apply Zmod_small; lia).
 destruct Z_lt_le_dec; unfold interp_carry.
   + replace [|r|] with r by (symmetry; apply Zmod_small; lia).
     rewrite Z.pow_2_r; lia.
   + replace [|r-wB|] with (r-wB) by (symmetry; apply Zmod_small; lia).
     rewrite Z.pow_2_r; lia.

 - assert (0<=Zneg p).
   { generalize (spec_to_Z x) (spec_to_Z y); nia. }
   lia.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma two_p_power2 : forall x, x>=0 -> two_p x = 2 ^ x.
 Proof.
 intros.
 unfold two_p.
 destruct x; simpl; auto.
 apply two_power_pos_correct.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition head0 x :=
   match [| x |] with
   | Z0 => zdigits
   | Zneg _ => 0
   | (Zpos _) as p => zdigits - Z.log2 p - 1
   end.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_head00:  forall x, [|x|] = 0 -> [|head0 x|] = Zpos digits.
 Proof. unfold head0; intros x ->; apply spec_zdigits. Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_head0  : forall x,  0 < [|x|] ->
         wB/ 2 <= 2 ^ ([|head0 x|]) * [|x|] < wB.
 Proof.
 intros; unfold head0.
 generalize (spec_to_Z x).
 destruct [|x|]; try discriminate.
 pose proof (Z.log2_nonneg (Zpos p)).
 destruct (Z.log2_spec (Zpos p)); auto.
 intros.
 assert (0 <= zdigits - Z.log2 (Zpos p) - 1 < wB) as Hrange. {
  split.
  - cut (Z.log2 (Zpos p) < zdigits).
    + lia.
    + unfold zdigits.
      unfold wB, base in *.
      apply Z.log2_lt_pow2; intuition.
  - apply Z.lt_trans with zdigits.
    + lia.
    + unfold zdigits, wB, base; apply Zpower2_lt_lin; auto with zarith.
 }

 unfold to_Z; rewrite (Zmod_small _ _ Hrange).
 split.
 - apply Z.le_trans with (2^(zdigits - Z.log2 (Zpos p) - 1)*(2^Z.log2 (Zpos p))).
   + apply Zdiv_le_upper_bound; auto with zarith.
     rewrite <- Zpower_exp; auto with zarith.
     rewrite Z.mul_comm; rewrite <- Z.pow_succ_r; auto with zarith.
     replace (Z.succ (zdigits - Z.log2 (Zpos p) -1 + Z.log2 (Zpos p))) with zdigits
       by ring.
     unfold wB, base, zdigits; auto with zarith.
   + apply Z.mul_le_mono_nonneg; auto with zarith.

 - apply Z.lt_le_trans
     with (2^(zdigits - Z.log2 (Zpos p) - 1)*(2^(Z.succ (Z.log2 (Zpos p))))).
   + apply Z.mul_lt_mono_pos_l; auto with zarith.
   + rewrite <- Zpower_exp; auto with zarith.
     replace (zdigits - Z.log2 (Zpos p) -1 +Z.succ (Z.log2 (Zpos p))) with zdigits
       by ring.
     unfold wB, base, zdigits; auto with zarith.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Fixpoint Ptail p := match p with
  | xO p => (Ptail p)+1
  | _ => 0
 end.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma Ptail_pos : forall p, 0 <= Ptail p.
 Proof.
 induction p; simpl; auto with zarith.
 Qed.
 #[local]
 Hint Resolve Ptail_pos : core.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma Ptail_bounded : forall p d, Zpos p < 2^(Zpos d) -> Ptail p < Zpos d.
 Proof.
 induction p; try (compute; auto; fail).
 intros; simpl.
 assert (d <> xH). {
  intro; subst.
  compute in H; destruct p; discriminate.
 }
 assert (Z.succ (Zpos (Pos.pred d)) = Zpos d). {
  simpl; f_equal.
  rewrite Pos.add_1_r.
  destruct (Pos.succ_pred_or d); auto.
  rewrite H1 in H0; elim H0; auto.
 }
 assert (Ptail p < Zpos (Pos.pred d)). {
  apply IHp.
  apply Z.mul_lt_mono_pos_r with 2; auto with zarith.
  rewrite (Z.mul_comm (Zpos p)).
  change (2 * Zpos p) with (Zpos p~0).
  rewrite Z.mul_comm.
  rewrite <- Z.pow_succ_r; auto with zarith.
  rewrite H1; auto.
 }
 rewrite <- H1; lia.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition tail0 x :=
  match [|x|] with
   | Z0 => zdigits
   | Zpos p => Ptail p
   | Zneg _ => 0
  end.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_tail00:  forall x, [|x|] = 0 -> [|tail0 x|] = Zpos digits.
 Proof.
  unfold tail0; intros.
  rewrite H; simpl.
  apply spec_zdigits.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_tail0  : forall x, 0 < [|x|] ->
         exists y, 0 <= y /\ [|x|] = (2 * y + 1) * (2 ^ [|tail0 x|]).
 Proof.
 intros; unfold tail0.
 generalize (spec_to_Z x).
 destruct [|x|]; try discriminate; intros.
 assert ([|Ptail p|] = Ptail p). {
  apply Zmod_small.
  split; auto.
  unfold wB, base in *.
  apply Z.lt_trans with (Zpos digits).
  - apply Ptail_bounded; auto with zarith.
  - apply Zpower2_lt_lin; auto with zarith.
 }
 rewrite H1.

 clear; induction p.
 - exists (Zpos p); simpl; rewrite Pos.mul_1_r; auto with zarith.
 - destruct IHp as (y & Yp & Ye).
   exists y.
   split; auto.
   change (Zpos p~0) with (2*Zpos p).
   rewrite Ye.
   change (Ptail p~0) with (Z.succ (Ptail p)).
   rewrite Z.pow_succ_r; auto; ring.

 - exists 0; simpl; auto with zarith.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition lor := Z.lor.
 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition land := Z.land.
 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition lxor := Z.lxor.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_lor x y : [|lor x y|] = Z.lor [|x|] [|y|].
 Proof.
 unfold lor, to_Z.
 apply Z.bits_inj'; intros n Hn. rewrite Z.lor_spec.
 unfold wB, base.
 destruct (Z.le_gt_cases (Z.pos digits) n).
 - rewrite !Z.mod_pow2_bits_high; auto with zarith.
 - rewrite !Z.mod_pow2_bits_low, Z.lor_spec; auto with zarith.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Lemma spec_land x y : [|land x y|] = Z.land [|x|] [|y|].
 Proof.
 unfold land, to_Z.
 apply Z.bits_inj'; intros n Hn. rewrite Z.land_spec.
 unfold wB, base.
 destruct (Z.le_gt_cases (Z.pos digits) n).
 - rewrite !Z.mod_pow2_bits_high; auto with zarith.
 - rewrite !Z.mod_pow2_bits_low, Z.land_spec; auto with zarith.
 Qed.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
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

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition zmod_ops : ZnZ.Ops Z := ZnZ.MkOps
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
 Existing Instance zmod_ops.

 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition zmod_specs : ZnZ.Specs zmod_ops := ZnZ.MkSpecs
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
 Existing Instance zmod_specs.

End ZModulo.

(** A modular version of the previous construction. *)

Module Type PositiveNotOne.
 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Parameter p : positive.
 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Axiom not_one : p <> 1%positive.
End PositiveNotOne.

Module ZModuloCyclicType (P:PositiveNotOne) <: CyclicType.
 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition t := Z.
#[global]
 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition ops : ZnZ.Ops t := zmod_ops P.p.
 Existing Instance ops.
#[global]
 #[deprecated(note="Cyclic.ZModulo will be moved to the test suite", since="8.17")]
 Definition specs : ZnZ.Specs ops := zmod_specs P.not_one.
 Existing Instance specs.
End ZModuloCyclicType.
