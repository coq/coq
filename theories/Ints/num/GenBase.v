
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

Set Implicit Arguments.

Require Import ZArith.
Require Import ZAux.
Require Import Basic_type.
Require Import JMeq.

Open Local Scope Z_scope.

Section GenBase.
 Variable w : Set.
 Variable w_0   : w.
 Variable w_1   : w.
 Variable w_Bm1 : w.
 Variable w_WW  : w -> w -> zn2z w.
 Variable w_0W  : w -> zn2z w.
 Variable w_digits : positive.
 Variable w_zdigits: w.
 Variable w_add: w -> w -> zn2z w.
 Variable w_to_Z   : w -> Z.
 Variable w_compare : w -> w -> comparison. 
 
 Definition ww_digits := xO w_digits.

 Definition ww_zdigits := w_add w_zdigits w_zdigits.

 Definition ww_to_Z := zn2z_to_Z (base w_digits) w_to_Z.

 Definition ww_1 := WW w_0 w_1.

 Definition ww_Bm1 := WW w_Bm1 w_Bm1.

 Definition ww_WW xh xl : zn2z (zn2z w) :=
  match xh, xl with
  | W0, W0 => W0
  | _, _ => WW xh xl
  end.
 
 Definition ww_W0 h : zn2z (zn2z w) :=
  match h with
  | W0 => W0
  | _ => WW h W0
  end.

 Definition ww_0W l : zn2z (zn2z w) :=
  match l with
  | W0 => W0
  | _ => WW W0 l
  end.
 
 Definition gen_WW (n:nat) := 
  match n return word w n -> word w n -> word w (S n) with 
  | O => w_WW 
  | S n =>
    fun (h l : zn2z (word w n)) =>
     match h, l with
     | W0, W0 => W0
     | _, _ => WW h l
     end
  end.

 Fixpoint gen_digits (n:nat) : positive := 
  match n with 
  | O => w_digits
  | S n => xO (gen_digits n)
  end.

 Definition gen_wB n := base (gen_digits n).

 Fixpoint gen_to_Z (n:nat) : word w n -> Z :=
  match n return word w n -> Z with
  | O => w_to_Z 
  | S n => zn2z_to_Z (gen_wB n) (gen_to_Z n)
  end.

 Fixpoint extend_aux (n:nat) (x:zn2z w) {struct n}: word w (S n) :=
  match n return word w (S n) with
  | O => x
  | S n1 => WW W0 (extend_aux n1 x)
  end.

 Definition extend (n:nat) (x:w) : word w (S n) :=
  let r := w_0W x in
  match r with
  | W0 => W0
  | _ => extend_aux n r
  end.

 Definition gen_0 n : word w n :=
   match n return word w n with 
   | O => w_0
   | S _ => W0
   end.
 
 Definition gen_split (n:nat) (x:zn2z (word w n)) :=
  match x with 
  | W0 => 
    match n return word w n * word w n with 
    | O => (w_0,w_0)
    | S _ => (W0, W0)
    end
  | WW h l => (h,l)
  end.
 
 Definition ww_compare x y :=
  match x, y with
  | W0, W0 => Eq
  | W0, WW yh yl =>
    match w_compare w_0 yh with
    | Eq => w_compare w_0 yl
    | _ => Lt
    end
  | WW xh xl, W0 =>
    match w_compare xh w_0 with
    | Eq => w_compare xl w_0
    | _ => Gt
    end
  | WW xh xl, WW yh yl =>
    match w_compare xh yh with
    | Eq => w_compare xl yl
    | Lt => Lt
    | Gt => Gt
    end
  end.


 (* Return the low part of the composed word*)
 Fixpoint get_low (n : nat) {struct n}:
  word w n -> w :=
  match n return (word w n -> w) with
  | 0%nat => fun x => x
  | S n1 =>
      fun x =>
      match x with
      | W0 => w_0
      | WW _ x1 => get_low n1 x1
      end
  end.

  
 Section GenProof.
  Notation wB  := (base w_digits).
  Notation wwB := (base ww_digits).
  Notation "[| x |]" := (w_to_Z x)  (at level 0, x at level 99).
  Notation "[[ x ]]" := (ww_to_Z x)  (at level 0, x at level 99).
  Notation "[+[ c ]]" := 
   (interp_carry 1 wwB ww_to_Z c) (at level 0, x at level 99).
  Notation "[-[ c ]]" := 
   (interp_carry (-1) wwB ww_to_Z c) (at level 0, x at level 99).
  Notation "[! n | x !]" := (gen_to_Z n x) (at level 0, x at level 99).

  Variable spec_w_0   : [|w_0|] = 0.
  Variable spec_w_1   : [|w_1|] = 1.
  Variable spec_w_Bm1 : [|w_Bm1|] = wB - 1.
  Variable spec_w_WW  : forall h l, [[w_WW h l]] = [|h|] * wB + [|l|].
  Variable spec_w_0W  : forall l, [[w_0W l]] = [|l|].
  Variable spec_to_Z  : forall x, 0 <= [|x|] < wB.
  Variable spec_w_compare : forall x y,
       match w_compare x y with
       | Eq => [|x|] = [|y|]
       | Lt => [|x|] < [|y|]
       | Gt => [|x|] > [|y|]
       end.

  Lemma wwB_wBwB : wwB = wB^2.
  Proof.
   unfold base, ww_digits;rewrite Zpower_2; rewrite (Zpos_xO w_digits).
   replace (2 * Zpos w_digits) with (Zpos w_digits + Zpos w_digits).
   apply Zpower_exp; unfold Zge;simpl;intros;discriminate.
   ring.
  Qed.

  Lemma spec_ww_1    : [[ww_1]] = 1.
  Proof. simpl;rewrite spec_w_0;rewrite spec_w_1;ring. Qed.

  Lemma spec_ww_Bm1  : [[ww_Bm1]] = wwB - 1.
  Proof. simpl;rewrite spec_w_Bm1;rewrite wwB_wBwB;ring. Qed.

  Lemma lt_0_wB : 0 < wB.
  Proof. 
   unfold base;apply Zpower_gt_0. unfold Zlt;reflexivity.
   unfold Zle;intros H;discriminate H.
  Qed.

  Lemma lt_0_wwB : 0 < wwB.
  Proof. rewrite wwB_wBwB; rewrite Zpower_2; apply Zmult_lt_0_compat;apply lt_0_wB. Qed.

  Lemma wB_pos: 1 < wB.
  Proof. 
   unfold base;apply Zlt_le_trans with (2^1).  unfold Zlt;reflexivity.
   apply Zpower_le_monotone.  unfold Zlt;reflexivity.
   split;unfold Zle;intros H. discriminate H.
   clear spec_w_0W w_0W spec_w_Bm1 spec_to_Z spec_w_WW w_WW.
   destruct w_digits; discriminate H.
  Qed.
 
  Lemma wwB_pos: 1 < wwB. 
  Proof.
   assert (H:= wB_pos);rewrite wwB_wBwB;rewrite <-(Zmult_1_r 1).
   rewrite Zpower_2.
   apply Zmult_lt_compat2;(split;[unfold Zlt;reflexivity|trivial]).
   apply Zlt_le_weak;trivial. 
  Qed.

  Theorem wB_div_2:  2 * (wB / 2) = wB.
  Proof.
   clear spec_w_0 w_0 spec_w_1 w_1 spec_w_Bm1 w_Bm1 spec_w_WW spec_w_0W 
    spec_to_Z;unfold base.
   assert (2 ^ Zpos w_digits = 2 * (2 ^ (Zpos w_digits - 1))).
   pattern 2 at 2; rewrite <- Zpower_1_r.
   rewrite <- Zpower_exp; auto with zarith.
   f_equal; auto with zarith.
   case w_digits; compute; intros; discriminate.
   rewrite H; f_equal; auto with zarith.
   rewrite Zmult_comm; apply Z_div_mult; auto with zarith.
  Qed.

  Theorem wwB_div_2 : wwB / 2 = wB / 2 * wB.
  Proof.
   clear spec_w_0 w_0 spec_w_1 w_1 spec_w_Bm1 w_Bm1 spec_w_WW spec_w_0W 
    spec_to_Z.
   rewrite wwB_wBwB; rewrite Zpower_2.
   pattern wB at 1; rewrite <- wB_div_2; auto.
   rewrite <- Zmult_assoc.
   repeat (rewrite (Zmult_comm 2); rewrite Z_div_mult); auto with zarith.
  Qed.

  Lemma mod_wwB : forall z x, 
   (z*wB + [|x|]) mod wwB = (z mod wB)*wB + [|x|].
  Proof.
   intros z x.
   rewrite Zplus_mod. 
   pattern wwB at 1;rewrite wwB_wBwB; rewrite Zpower_2.
   rewrite Zmult_mod_distr_r;try apply lt_0_wB.
   rewrite (Zmod_small [|x|]).
   apply Zmod_small;rewrite wwB_wBwB;apply beta_mult;try apply spec_to_Z.
   apply Z_mod_lt;apply Zlt_gt;apply lt_0_wB.
   destruct (spec_to_Z x);split;trivial.
   change [|x|] with (0*wB+[|x|]). rewrite wwB_wBwB.
   rewrite Zpower_2;rewrite <- (Zplus_0_r (wB*wB));apply beta_lex_inv.
   apply lt_0_wB. apply spec_to_Z. split;[apply Zle_refl | apply lt_0_wB].
 Qed.

  Lemma wB_div : forall x y, ([|x|] * wB + [|y|]) / wB = [|x|].
  Proof.
   clear spec_w_0 spec_w_1 spec_w_Bm1 w_0 w_1 w_Bm1.
   intros x y;unfold base;rewrite Zdiv_shift_r;auto with zarith.
   rewrite Z_div_mult;auto with zarith.
   destruct (spec_to_Z x);trivial.
  Qed.

  Lemma wB_div_plus : forall x y p, 
   0 <= p -> 
   ([|x|]*wB + [|y|]) / 2^(Zpos w_digits + p) = [|x|] / 2^p.
  Proof.
   clear spec_w_0 spec_w_1 spec_w_Bm1 w_0 w_1 w_Bm1.
   intros x y p Hp;rewrite Zpower_exp;auto with zarith.
   rewrite <- Zdiv_Zdiv;auto with zarith.
   rewrite wB_div;trivial.
  Qed.

  Lemma lt_wB_wwB : wB < wwB.
  Proof.
   clear spec_w_0 spec_w_1 spec_w_Bm1 w_0 w_1 w_Bm1.
   unfold base;apply Zpower_lt_monotone;auto with zarith.
   assert (0 < Zpos w_digits). compute;reflexivity.
   unfold ww_digits;rewrite Zpos_xO;auto with zarith.
  Qed.
 
  Lemma w_to_Z_wwB : forall x, x < wB -> x < wwB.
  Proof.
   intros x H;apply Zlt_trans with wB;trivial;apply lt_wB_wwB.
  Qed.

  Lemma spec_ww_to_Z : forall x, 0 <= [[x]] < wwB.
  Proof.
   clear spec_w_0 spec_w_1 spec_w_Bm1 w_0 w_1 w_Bm1.
   destruct x as [ |h l];simpl.
   split;[apply Zle_refl|apply lt_0_wwB].
   assert (H:=spec_to_Z h);assert (L:=spec_to_Z l);split.
   apply Zplus_le_0_compat;auto with zarith.
   rewrite <- (Zplus_0_r wwB);rewrite wwB_wBwB; rewrite Zpower_2;
    apply beta_lex_inv;auto with zarith.
  Qed.

  Lemma gen_wB_wwB : forall n, gen_wB n * gen_wB n = gen_wB (S n).
  Proof.
   intros n;unfold gen_wB;simpl.
   unfold base;rewrite (Zpos_xO (gen_digits n)).
   replace  (2 * Zpos (gen_digits n)) with 
     (Zpos (gen_digits n) + Zpos (gen_digits n)).
   symmetry; apply Zpower_exp;intro;discriminate.
   ring.
  Qed.

  Lemma gen_wB_pos:
   forall n, 0 <= gen_wB n.
 Proof.
 intros n; unfold gen_wB, base; auto with zarith.
 Qed.

  Lemma gen_wB_more_digits:
  forall n, wB <= gen_wB n.
  Proof.
  clear spec_w_0 spec_w_1 spec_w_Bm1 w_0 w_1 w_Bm1.
  intros n; elim n; clear n; auto.
    unfold gen_wB, gen_digits; auto with zarith.
  intros n H1; rewrite <- gen_wB_wwB.
  apply Zle_trans with (wB * 1).
    rewrite Zmult_1_r; apply Zle_refl.
  apply Zmult_le_compat; auto with zarith.
  apply Zle_trans with wB; auto with zarith.
  unfold base.
  rewrite <- (Zpower_0_r 2).
  apply Zpower_le_monotone2; auto with zarith.
  unfold base; auto with zarith.
  Qed.

  Lemma spec_gen_to_Z : 
   forall n (x:word w n), 0 <= [!n | x!] < gen_wB n.
  Proof.
  clear spec_w_0 spec_w_1 spec_w_Bm1 w_0 w_1 w_Bm1.
  induction n;intros. exact (spec_to_Z x).
  unfold gen_to_Z;fold gen_to_Z.
  destruct x;unfold zn2z_to_Z.
  unfold gen_wB,base;split;auto with zarith.
  assert (U0:= IHn w0);assert (U1:= IHn w1).
  split;auto with zarith.
  apply Zlt_le_trans with ((gen_wB n - 1) * gen_wB n + gen_wB n).
  assert (gen_to_Z n w0*gen_wB n <= (gen_wB n - 1)*gen_wB n).
  apply Zmult_le_compat_r;auto with zarith.
  auto with zarith.
  rewrite <- gen_wB_wwB.
  replace ((gen_wB n - 1) * gen_wB n + gen_wB n) with (gen_wB n * gen_wB n);
   [auto with zarith | ring].
  Qed.

  Lemma spec_get_low:
  forall n x, 
     [!n | x!] < wB ->  [|get_low n x|] = [!n | x!].
  Proof.
  clear spec_w_1 spec_w_Bm1.
  intros n; elim n; auto; clear n.
  intros n Hrec x; case x; clear x; auto.
  intros xx yy H1; simpl in H1.
  assert (F1: [!n | xx!] = 0).
    case (Zle_lt_or_eq 0 ([!n | xx!])); auto.
      case (spec_gen_to_Z n xx); auto.
     intros F2.
     assert (F3 := gen_wB_more_digits n).
    assert (F4: 0 <= [!n | yy!]).
      case (spec_gen_to_Z n yy); auto.
    assert (F5: 1 * wB <=  [!n | xx!] * gen_wB n);
     auto with zarith.
    apply Zmult_le_compat; auto with zarith.
    unfold base; auto with zarith.
  simpl get_low; simpl gen_to_Z.
  generalize H1; clear H1.
  rewrite F1; rewrite Zmult_0_l; rewrite Zplus_0_l.
  intros H1; apply Hrec; auto.
  Qed.

  Lemma spec_gen_WW : forall n (h l : word w n),
    [!S n|gen_WW n h l!] = [!n|h!] * gen_wB n + [!n|l!].
  Proof.
   induction n;simpl;intros;trivial.
   destruct h;auto.
   destruct l;auto.
  Qed.

  Lemma spec_extend_aux : forall n x, [!S n|extend_aux n x!] = [[x]].
  Proof. induction n;simpl;trivial. Qed. 

  Lemma spec_extend : forall n x, [!S n|extend n x!] = [|x|].
  Proof. 
   intros n x;assert (H:= spec_w_0W x);unfold extend.
   destruct (w_0W x);simpl;trivial. 
   rewrite <- H;exact (spec_extend_aux n (WW w0 w1)).
  Qed.

  Lemma spec_gen_0 : forall n, [!n|gen_0 n!] = 0.
  Proof. destruct n;trivial. Qed.

  Lemma spec_gen_split : forall n x, 
   let (h,l) := gen_split n x in
   [!S n|x!] = [!n|h!] * gen_wB n + [!n|l!].
  Proof.
   destruct x;simpl;auto.
   destruct n;simpl;trivial.
   rewrite spec_w_0;trivial.
  Qed.

  Lemma wB_lex_inv: forall a b c d, 
      a < c -> 
      a * wB + [|b|] < c  * wB + [|d|]. 
  Proof.
   intros a b c d H1; apply beta_lex_inv with (1 := H1); auto.
  Qed.

  Lemma spec_ww_compare : forall x y,
       match ww_compare x y with
       | Eq => [[x]] = [[y]]
       | Lt => [[x]] < [[y]]
       | Gt => [[x]] > [[y]]
       end.
  Proof.
   destruct x as [ |xh xl];destruct y as [ |yh yl];simpl;trivial.
   generalize (spec_w_compare w_0 yh);destruct (w_compare w_0 yh);
    intros H;rewrite spec_w_0 in H.
   rewrite <- H;simpl;rewrite <- spec_w_0;apply spec_w_compare.
   change 0 with (0*wB+0);pattern 0 at 2;rewrite <- spec_w_0.
   apply wB_lex_inv;trivial. 
   absurd (0 <= [|yh|]). apply Zgt_not_le;trivial.
   destruct (spec_to_Z yh);trivial.
   generalize (spec_w_compare xh w_0);destruct (w_compare xh w_0);
    intros H;rewrite spec_w_0 in H.
   rewrite H;simpl;rewrite <- spec_w_0;apply spec_w_compare.
   absurd (0 <= [|xh|]). apply Zgt_not_le;apply Zlt_gt;trivial.
   destruct (spec_to_Z xh);trivial.
   apply Zlt_gt;change 0 with (0*wB+0);pattern 0 at 2;rewrite <- spec_w_0.
   apply wB_lex_inv;apply Zgt_lt;trivial. 
  
   generalize (spec_w_compare xh yh);destruct (w_compare xh yh);intros H.
   rewrite H;generalize (spec_w_compare xl yl);destruct (w_compare xl yl);
   intros H1;[rewrite H1|apply Zplus_lt_compat_l|apply Zplus_gt_compat_l];
   trivial.
   apply wB_lex_inv;trivial.
   apply Zlt_gt;apply wB_lex_inv;apply Zgt_lt;trivial.
  Qed.

   
 End GenProof.

End GenBase.

