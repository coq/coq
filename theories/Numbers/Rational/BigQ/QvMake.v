(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

(*i $Id$ i*)

Require Import Bool.
Require Import ZArith.
Require Import Znumtheory.
Require Import BigNumPrelude.
Require Import Arith.
Require Export BigN.
Require Export BigZ.
Require Import QArith.
Require Import Qcanon.
Require Import Qpower.
Require Import QMake_base.

Module Qv.

 Import BinInt Zorder.
 Open Local Scope Q_scope.
 Open Local Scope Qc_scope.

 (** The notation of a rational number is either an integer x,
     interpreted as itself or a pair (x,y) of an integer x and a naturel
     number y interpreted as x/y. All functions maintain the invariant
     that y is never zero. *)

 Definition t := q_type.

 Definition zero: t := Qz BigZ.zero.
 Definition one: t := Qz BigZ.one.
 Definition minus_one: t := Qz BigZ.minus_one.

 Definition of_Z x: t := Qz (BigZ.of_Z x).

 Definition wf x := 
  match x with
  | Qz _ => True
  | Qq n d => if BigN.eq_bool d BigN.zero then False else True
  end.

 Definition of_Q q: t := 
 match q with x # y =>
  Qq (BigZ.of_Z x) (BigN.of_N (Npos y))
 end.

 Definition of_Qc q := of_Q (this q).

 Definition to_Q (q: t) := 
 match q with 
  Qz x => BigZ.to_Z x # 1
 |Qq x y => BigZ.to_Z x # Z2P (BigN.to_Z y)
 end.

 Definition to_Qc q := !!(to_Q q).

 Notation "[[ x ]]" := (to_Qc x).

 Notation "[ x ]" := (to_Q x).

 Theorem spec_to_Q: forall q: Q, [of_Q q] = q.
 intros (x,y); simpl.
 rewrite BigZ.spec_of_Z; simpl.
 rewrite (BigN.spec_of_pos); auto.
 Qed.

 Theorem spec_to_Qc: forall q, [[of_Qc q]] = q.
 intros (x, Hx); unfold of_Qc, to_Qc; simpl.
 apply Qc_decomp; simpl.
 intros; rewrite spec_to_Q; auto.
 Qed.

 Definition opp (x: t): t :=
  match x with
  | Qz zx => Qz (BigZ.opp zx)
  | Qq nx dx => Qq (BigZ.opp nx) dx
  end.

 Theorem wf_opp: forall x, wf x -> wf (opp x).
 intros [zx | nx dx]; unfold opp, wf; auto.
 Qed.

 Theorem spec_opp: forall q, ([opp q] = -[q])%Q.
 intros [z | x y]; simpl.
 rewrite BigZ.spec_opp; auto.
 rewrite BigZ.spec_opp; auto.
 Qed.

 Theorem spec_oppc: forall q, [[opp q]] = -[[q]].
 intros q; unfold Qcopp, to_Qc, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 rewrite spec_opp.
 rewrite <- Qred_opp.
 rewrite Qred_involutive; auto.
 Qed.

 (* Les fonctions doivent assurer que si leur arguments sont valides alors
    le resultat est correct et valide (si c'est un Q) 
 *)

 Definition compare (x y: t) :=
  match x, y with
  | Qz zx, Qz zy => BigZ.compare zx zy
  | Qz zx, Qq ny dy => BigZ.compare (BigZ.mul zx (BigZ.Pos dy)) ny
  | Qq nx dx, Qz zy => BigZ.compare nx (BigZ.mul zy (BigZ.Pos dx))  
  | Qq nx dx, Qq ny dy => BigZ.compare (BigZ.mul nx (BigZ.Pos dy)) (BigZ.mul ny (BigZ.Pos dx))
  end.

 Theorem spec_compare: forall q1 q2, wf q1 -> wf q2 ->
  compare q1 q2 = ([q1] ?= [q2])%Q.
 intros [z1 | x1 y1] [z2 | x2 y2]; 
   unfold Qcompare, compare, to_Q, Qnum, Qden, wf.
 repeat rewrite Zmult_1_r.
 generalize (BigZ.spec_compare z1 z2); case BigZ.compare; intros H; auto.
 rewrite H; rewrite Zcompare_refl; auto.
 rewrite Zmult_1_r.
 generalize (BigN.spec_eq_bool y2 BigN.zero);
   case BigN.eq_bool.
   intros _ _ HH; case HH.
 rewrite BigN.spec_0; intros HH _ _.
 rewrite Z2P_correct; auto with zarith.
  2: generalize (BigN.spec_pos y2); auto with zarith.
 generalize (BigZ.spec_compare (z1 * BigZ.Pos y2) x2)%bigZ; case BigZ.compare;
   rewrite BigZ.spec_mul; simpl; intros H; apply sym_equal; auto.
 rewrite H; rewrite Zcompare_refl; auto.
 generalize (BigN.spec_eq_bool y1 BigN.zero);
   case BigN.eq_bool.
   intros _ HH; case HH.
 rewrite BigN.spec_0; intros HH _ _.
 rewrite Z2P_correct; auto with zarith.
  2: generalize (BigN.spec_pos y1); auto with zarith.
 rewrite Zmult_1_r.
 generalize (BigZ.spec_compare x1 (z2 * BigZ.Pos y1))%bigZ; case BigZ.compare;
   rewrite BigZ.spec_mul; simpl; intros H; apply sym_equal; auto.
 rewrite H; rewrite Zcompare_refl; auto.
 generalize (BigN.spec_eq_bool y1 BigN.zero);
   case BigN.eq_bool.
   intros _ HH; case HH.
 rewrite BigN.spec_0; intros HH1. 
 generalize (BigN.spec_eq_bool y2 BigN.zero);
   case BigN.eq_bool.
   intros _ _ HH; case HH.
 rewrite BigN.spec_0; intros HH2 _ _.
 repeat rewrite Z2P_correct.
  2: generalize (BigN.spec_pos y1); auto with zarith.
  2: generalize (BigN.spec_pos y2); auto with zarith.
 generalize (BigZ.spec_compare (x1 * BigZ.Pos y2) 
                               (x2 * BigZ.Pos y1))%bigZ; case BigZ.compare;
   repeat rewrite BigZ.spec_mul; simpl; intros H; apply sym_equal; auto.
 rewrite H; rewrite Zcompare_refl; auto.
 Qed.

 Theorem spec_comparec: forall q1 q2, wf q1 -> wf q2 ->
  compare q1 q2 = ([[q1]] ?= [[q2]]).
 unfold Qccompare, to_Qc. 
 intros q1 q2 Hq1 Hq2; rewrite spec_compare; simpl; auto.
 apply Qcompare_comp; apply Qeq_sym; apply Qred_correct.
 Qed.

 Definition norm n d: t :=
  if BigZ.eq_bool n BigZ.zero then zero
  else
    let gcd := BigN.gcd (BigZ.to_N n) d in
    if BigN.eq_bool gcd BigN.one then Qq n d
    else	
      let n := BigZ.div n (BigZ.Pos gcd) in
      let d := BigN.div d gcd in
      if BigN.eq_bool d BigN.one then Qz n
      else Qq n d.

 Theorem wf_norm: forall n q,
   (BigN.to_Z q <> 0)%Z -> wf (norm n q).
 intros p q; unfold norm, wf; intros Hq.
 assert (Hp := BigN.spec_pos (BigZ.to_N p)).
 match goal with  |- context[BigZ.eq_bool ?X ?Y] => 
   generalize (BigZ.spec_eq_bool X Y); case BigZ.eq_bool
 end; auto; rewrite BigZ.spec_0; intros H1.
 simpl; auto.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_1.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_1.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_0.
 set (a := BigN.to_Z (BigZ.to_N p)).
 set (b := (BigN.to_Z q)).
 assert (F: (0 < Zgcd a b)%Z).
   case (Zle_lt_or_eq _ _ (Zgcd_is_pos a b)); auto.
   intros HH1; case Hq; apply (Zgcd_inv_0_r _ _ (sym_equal HH1)).
 rewrite BigN.spec_div; rewrite BigN.spec_gcd; auto; fold a; fold b.
 intros H; case Hq; fold b.
 rewrite (Zdivide_Zdiv_eq (Zgcd a b) b); auto.
 rewrite H; auto with zarith.
 assert (F1:= Zgcd_is_gcd a b); inversion F1; auto.
 Qed.
 
 Theorem spec_norm: forall n q, 
    ((0 < BigN.to_Z q)%Z -> [norm n q] == [Qq n q])%Q.
 intros p q; unfold norm; intros Hq.
 assert (Hp := BigN.spec_pos (BigZ.to_N p)).
 match goal with  |- context[BigZ.eq_bool ?X ?Y] => 
   generalize (BigZ.spec_eq_bool X Y); case BigZ.eq_bool
 end; auto; rewrite BigZ.spec_0; intros H1.
   red; simpl; rewrite H1; ring.
 case (Zle_lt_or_eq _ _ Hp); clear Hp; intros Hp.
 case (Zle_lt_or_eq _ _ 
      (Zgcd_is_pos (BigN.to_Z (BigZ.to_N p)) (BigN.to_Z q))); intros H4.
 2: generalize Hq; rewrite (Zgcd_inv_0_r _ _ (sym_equal H4)); auto with zarith.
 2: red; simpl; auto with zarith.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_1; intros H2.
   apply Qeq_refl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_1.
 red; simpl.
 rewrite BigZ.spec_div; simpl; rewrite BigN.spec_gcd; auto with zarith.
 rewrite BigN.spec_div; simpl; rewrite BigN.spec_gcd; auto with zarith.
 rewrite Zmult_1_r.
 rewrite Z2P_correct; auto with zarith.
 rewrite spec_to_N; intros; rewrite Zgcd_div_swap; auto.
 rewrite H; ring.
 intros H3.
 red; simpl.
 rewrite BigZ.spec_div; simpl; rewrite BigN.spec_gcd; auto with zarith.
 assert (F: (0 < BigN.to_Z (q / BigN.gcd (BigZ.to_N p) q)%bigN)%Z).
   rewrite BigN.spec_div; auto with zarith.
   rewrite BigN.spec_gcd.
   apply Zgcd_div_pos; auto.
   rewrite BigN.spec_gcd; auto.
 rewrite Z2P_correct; auto.
 rewrite Z2P_correct; auto.
 rewrite BigN.spec_div; simpl; rewrite BigN.spec_gcd; auto with zarith.
 rewrite spec_to_N; apply Zgcd_div_swap; auto.
 case H1; rewrite spec_to_N; rewrite <- Hp; ring.
 Qed.

 Theorem spec_normc: forall n q, 
    (0 < BigN.to_Z q)%Z -> [[norm n q]] = [[Qq n q]].
 intros n q H; unfold to_Qc, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_norm; auto.
 Qed.
      
 Definition add (x y: t): t :=
  match x, y with
  | Qz zx, Qz zy => Qz (BigZ.add zx zy)
  | Qz zx, Qq ny dy => Qq (BigZ.add (BigZ.mul zx (BigZ.Pos dy)) ny) dy
  | Qq nx dx, Qz zy => Qq (BigZ.add nx (BigZ.mul zy (BigZ.Pos dx))) dx
  | Qq nx dx, Qq ny dy => 
    let n := BigZ.add (BigZ.mul nx (BigZ.Pos dy)) (BigZ.mul ny (BigZ.Pos dx)) in
    let d := BigN.mul dx dy in
    Qq n d
  end.

 Theorem wf_add: forall x y, wf x -> wf y -> wf (add x y).
 intros [zx | nx dx] [zy | ny dy]; unfold add, wf; auto.
 repeat match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_0; rewrite BigN.spec_mul.
 intros H1 H2 H3.
 case (Zmult_integral _ _ H1); auto with zarith.
 Qed.

 Theorem spec_add x y: wf x -> wf y ->
  ([add x y] == [x] + [y])%Q.
 intros [x | nx dx] [y | ny dy]; unfold Qplus; simpl.
 rewrite BigZ.spec_add; repeat rewrite Zmult_1_r; auto.
  intros; apply Qeq_refl; auto.
 assert (F1:= BigN.spec_pos dy).
 rewrite Zmult_1_r.
 generalize (BigN.spec_eq_bool dy BigN.zero);
   case BigN.eq_bool.
   intros _ _ HH; case HH.
 rewrite BigN.spec_0; intros HH _ _.
 rewrite Z2P_correct; auto with zarith.
 rewrite BigZ.spec_add; rewrite BigZ.spec_mul.
 simpl; apply Qeq_refl.
 generalize (BigN.spec_eq_bool dx BigN.zero);
   case BigN.eq_bool.
   intros _ HH; case HH.
 rewrite BigN.spec_0; intros HH _ _.
 assert (F1:= BigN.spec_pos dx).
 rewrite Zmult_1_r; rewrite Pmult_1_r.
 simpl; rewrite Z2P_correct; auto with zarith.
 rewrite BigZ.spec_add; rewrite BigZ.spec_mul; simpl.
 apply Qeq_refl.
 generalize (BigN.spec_eq_bool dx BigN.zero);
   case BigN.eq_bool.
   intros _ HH; case HH.
 rewrite BigN.spec_0; intros HH1.
 generalize (BigN.spec_eq_bool dy BigN.zero);
   case BigN.eq_bool.
   intros _ _ HH; case HH.
 rewrite BigN.spec_0; intros HH2 _ _.
 assert (Fx: (0 < BigN.to_Z dx)%Z).
   generalize (BigN.spec_pos dx); auto with zarith.
 assert (Fy: (0 < BigN.to_Z dy)%Z).
   generalize (BigN.spec_pos dy); auto with zarith.
 rewrite BigZ.spec_add; repeat rewrite BigN.spec_mul.
 red; simpl.
 rewrite Zpos_mult_morphism.
 repeat rewrite Z2P_correct; auto.
 repeat rewrite BigZ.spec_mul; simpl; auto.
 apply Zmult_lt_0_compat; auto.
 Qed.

 Theorem spec_addc x y: wf x -> wf y ->
  [[add x y]] = [[x]] + [[y]].
 intros x y H1 H2; unfold to_Qc.
 apply trans_equal with (!! ([x] + [y])).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_add; auto.
 unfold Qcplus, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 apply Qplus_comp; apply Qeq_sym; apply Qred_correct.
 Qed.

 Definition add_norm (x y: t): t := 
  match x, y with
  | Qz zx, Qz zy => Qz (BigZ.add zx zy)
  | Qz zx, Qq ny dy => 
    norm (BigZ.add (BigZ.mul zx (BigZ.Pos dy)) ny) dy 
  | Qq nx dx, Qz zy =>
    norm (BigZ.add (BigZ.mul zy (BigZ.Pos dx)) nx) dx
  | Qq nx dx, Qq ny dy =>
    let n := BigZ.add (BigZ.mul nx (BigZ.Pos dy)) (BigZ.mul ny (BigZ.Pos dx)) in
    let d := BigN.mul dx dy in
    norm n d 
  end.

 Theorem wf_add_norm: forall x y, wf x -> wf y -> wf (add_norm x y).
 intros [zx | nx dx] [zy | ny dy]; unfold add_norm; auto.
 intros HH1 HH2; apply wf_norm.
 generalize HH2; simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto.
 intros HH1 HH2; apply wf_norm.
 generalize HH1; simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto.
 intros HH1 HH2; apply wf_norm.
 rewrite BigN.spec_mul; intros HH3.
 case (Zmult_integral _ _ HH3).
 generalize HH1; simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto.
 generalize HH2; simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto.
 Qed.

 Theorem spec_add_norm x y: wf x -> wf y ->
  ([add_norm x y] == [x] + [y])%Q.
 intros x y H1 H2; rewrite <- spec_add; auto.
 generalize H1 H2; unfold add_norm, add, wf; case x; case y; clear H1 H2.
  intros; apply Qeq_refl.
 intros p1 n p2 _.
 generalize (BigN.spec_eq_bool n BigN.zero);
   case BigN.eq_bool.
   intros _ HH; case HH.
 rewrite BigN.spec_0; intros HH _.
 match goal with |- [norm ?X ?Y] == _ =>
  apply Qeq_trans with ([Qq X Y]);
  [apply spec_norm | idtac]
 end.
 generalize (BigN.spec_pos n); auto with zarith.
 simpl.
 repeat rewrite BigZ.spec_add.
 repeat rewrite BigZ.spec_mul; simpl.
 apply Qeq_refl.
 intros p1 n p2.
 generalize (BigN.spec_eq_bool p2 BigN.zero);
   case BigN.eq_bool.
   intros _ HH; case HH.
 rewrite BigN.spec_0; intros HH _ _.
 match goal with |- [norm ?X ?Y] == _ =>
  apply Qeq_trans with ([Qq X Y]);
  [apply spec_norm | idtac]
 end.
 generalize (BigN.spec_pos p2); auto with zarith.
 simpl.
 repeat rewrite BigZ.spec_add.
 repeat rewrite BigZ.spec_mul; simpl.
 rewrite Zplus_comm.
 apply Qeq_refl.
 intros p1 q1 p2 q2.
 generalize (BigN.spec_eq_bool q2 BigN.zero);
   case BigN.eq_bool.
   intros _ HH; case HH.
 rewrite BigN.spec_0; intros HH1 _.
 generalize (BigN.spec_eq_bool q1 BigN.zero);
   case BigN.eq_bool.
   intros _ HH; case HH.
 rewrite BigN.spec_0; intros HH2 _.
 match goal with |- [norm ?X ?Y] == _ =>
  apply Qeq_trans with ([Qq X Y]);
  [apply spec_norm | idtac]
 end; try apply Qeq_refl.
 rewrite BigN.spec_mul.
 apply Zmult_lt_0_compat.
  generalize (BigN.spec_pos q2); auto with zarith.
  generalize (BigN.spec_pos q1); auto with zarith.
 Qed.

 Theorem spec_add_normc x y: wf x -> wf y ->
  [[add_norm x y]] = [[x]] + [[y]].
 intros x y Hx Hy; unfold to_Qc.
 apply trans_equal with (!! ([x] + [y])).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_add_norm; auto.
 unfold Qcplus, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 apply Qplus_comp; apply Qeq_sym; apply Qred_correct.
 Qed.

 Definition sub x y := add x (opp y).

 Theorem wf_sub x y: wf x -> wf y -> wf (sub x y).
 intros x y Hx Hy; unfold sub; apply wf_add; auto.
 apply wf_opp; auto.
 Qed.

 Theorem spec_sub x y: wf x -> wf y ->
  ([sub x y] == [x] - [y])%Q.
 intros x y Hx Hy; unfold sub; rewrite spec_add; auto.
 rewrite spec_opp; ring.
 apply wf_opp; auto.
 Qed.

 Theorem spec_subc x y: wf x -> wf y ->
   [[sub x y]] = [[x]] - [[y]].
 intros x y Hx Hy; unfold sub; rewrite spec_addc; auto.
 rewrite spec_oppc; ring.
 apply wf_opp; auto.
 Qed.

 Definition sub_norm x y := add_norm x (opp y).

 Theorem wf_sub_norm x y: wf x -> wf y -> wf (sub_norm x y).
 intros x y Hx Hy; unfold sub_norm; apply wf_add_norm; auto.
 apply wf_opp; auto.
 Qed.

 Theorem spec_sub_norm x y: wf x -> wf y ->
  ([sub_norm x y] == [x] - [y])%Q.
 intros x y Hx Hy; unfold sub_norm; rewrite spec_add_norm; auto.
 rewrite spec_opp; ring.
 apply wf_opp; auto.
 Qed.

 Theorem spec_sub_normc x y: wf x -> wf y ->
   [[sub_norm x y]] = [[x]] - [[y]].
 intros x y Hx Hy; unfold sub_norm; rewrite spec_add_normc; auto.
 rewrite spec_oppc; ring.
 apply wf_opp; auto.
 Qed.

 Definition mul (x y: t): t :=
  match x, y with
  | Qz zx, Qz zy => Qz (BigZ.mul zx zy)
  | Qz zx, Qq ny dy => Qq (BigZ.mul zx ny) dy
  | Qq nx dx, Qz zy => Qq (BigZ.mul nx zy) dx
  | Qq nx dx, Qq ny dy => 
    Qq (BigZ.mul nx ny) (BigN.mul dx dy)
  end.

 Theorem wf_mul: forall x y, wf x -> wf y -> wf (mul x y).
 intros [zx | nx dx] [zy | ny dy]; unfold mul, wf; auto.
 repeat match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_0; rewrite BigN.spec_mul.
 intros H1 H2 H3.
 case (Zmult_integral _ _ H1); auto with zarith.
 Qed.

 Theorem spec_mul x y: wf x -> wf y -> ([mul x y] == [x] * [y])%Q.
 intros [x | nx dx] [y | ny dy]; unfold Qmult; simpl.
 rewrite BigZ.spec_mul; repeat rewrite Zmult_1_r; auto.
  intros; apply Qeq_refl; auto.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto.
 intros _ _ HH; case HH.
 rewrite BigN.spec_0; intros HH1 _ _.
 rewrite BigZ.spec_mul; apply Qeq_refl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto.
 intros _ HH; case HH.
 rewrite BigN.spec_0; intros HH1 _ _.
 rewrite BigZ.spec_mul; rewrite Pmult_1_r.
 apply Qeq_refl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto.
 intros _ HH; case HH.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto.
 intros _ _ _ HH; case HH.
 rewrite BigN.spec_0; intros H1 H2 _ _.
 rewrite BigZ.spec_mul; rewrite BigN.spec_mul.
 assert (tmp: 
  (forall a b, 0 < a -> 0 < b -> Z2P (a * b) = (Z2P a * Z2P b)%positive)%Z).
  intros [|a|a] [|b|b]; simpl; auto; intros; apply False_ind; auto with zarith.
 rewrite tmp; auto.
 apply Qeq_refl.
  generalize (BigN.spec_pos dx); auto with zarith.
  generalize (BigN.spec_pos dy); auto with zarith.
 Qed.

 Theorem spec_mulc x y: wf x -> wf y ->
  [[mul x y]] = [[x]] * [[y]].
 intros x y Hx Hy; unfold to_Qc.
 apply trans_equal with (!! ([x] * [y])).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_mul; auto.
 unfold Qcmult, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 apply Qmult_comp; apply Qeq_sym; apply Qred_correct.
 Qed.

 Definition mul_norm (x y: t): t := 
  match x, y with
  | Qz zx, Qz zy => Qz (BigZ.mul zx zy)
  | Qz zx, Qq ny dy =>
    if BigZ.eq_bool zx BigZ.zero then zero
    else	
      let gcd := BigN.gcd (BigZ.to_N zx) dy in
      if BigN.eq_bool gcd BigN.one then Qq (BigZ.mul zx ny) dy
      else 
        let zx := BigZ.div zx (BigZ.Pos gcd) in
        let d := BigN.div dy gcd in
        if BigN.eq_bool d BigN.one then Qz (BigZ.mul zx ny)
        else Qq (BigZ.mul zx ny) d
  | Qq nx dx, Qz zy =>   
    if BigZ.eq_bool zy BigZ.zero then zero
    else	
      let gcd := BigN.gcd (BigZ.to_N zy) dx in
      if BigN.eq_bool gcd BigN.one then Qq (BigZ.mul zy nx) dx
      else 
        let zy := BigZ.div zy (BigZ.Pos gcd) in
        let d := BigN.div dx gcd in
        if BigN.eq_bool d BigN.one then Qz (BigZ.mul zy nx)
        else Qq (BigZ.mul zy nx) d
  | Qq nx dx, Qq ny dy => norm (BigZ.mul nx ny) (BigN.mul dx dy)
  end.

 Theorem wf_mul_norm: forall x y, wf x -> wf y -> wf (mul_norm x y).
 intros [zx | nx dx] [zy | ny dy]; unfold mul_norm; auto.
 intros HH1 HH2.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto;
 match goal with  |- context[BigZ.eq_bool ?X ?Y] => 
   generalize (BigZ.spec_eq_bool X Y); case BigZ.eq_bool
 end; auto.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto.
 rewrite BigN.spec_1; rewrite BigZ.spec_0.
 intros H1 H2; unfold wf.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto.
 rewrite BigN.spec_0.
 set (a := BigN.to_Z (BigZ.to_N zx)).
 set (b := (BigN.to_Z dy)).
 assert (F: (0 < Zgcd a b)%Z).
   case (Zle_lt_or_eq _ _ (Zgcd_is_pos a b)); auto.
   intros HH3; case H2; rewrite spec_to_N; fold a.
   rewrite (Zgcd_inv_0_l _ _ (sym_equal HH3)); try ring.
 rewrite BigN.spec_div; rewrite BigN.spec_gcd; fold a; fold b; auto.
 intros H.
 generalize HH2; simpl wf.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto.
 rewrite BigN.spec_0; intros HH; case HH; fold b.
 rewrite (Zdivide_Zdiv_eq (Zgcd a b) b); auto.
 rewrite H; auto with zarith.
 assert (F1:= Zgcd_is_gcd a b); inversion F1; auto.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto.
 rewrite BigN.spec_1; rewrite BigN.spec_gcd.
 intros HH1 H1 H2.
 match goal with  |- context[BigZ.eq_bool ?X ?Y] => 
   generalize (BigZ.spec_eq_bool X Y); case BigZ.eq_bool
 end; auto.
 rewrite BigN.spec_1; rewrite BigN.spec_gcd.
 intros HH1 H1 H2.
 match goal with  |- context[BigZ.eq_bool ?X ?Y] => 
   generalize (BigZ.spec_eq_bool X Y); case BigZ.eq_bool
 end; auto.
 rewrite BigZ.spec_0.
 intros HH2.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto.
 set (a := BigN.to_Z (BigZ.to_N zy)).
 set (b := (BigN.to_Z dx)).
 assert (F: (0 < Zgcd a b)%Z).
   case (Zle_lt_or_eq _ _ (Zgcd_is_pos a b)); auto.
   intros HH3; case HH2; rewrite spec_to_N; fold a.
   rewrite (Zgcd_inv_0_l _ _ (sym_equal HH3)); try ring.
 rewrite BigN.spec_div; rewrite BigN.spec_gcd; fold a; fold b; auto.
 intros H; unfold wf.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto.
 rewrite BigN.spec_0.
 rewrite BigN.spec_div; rewrite BigN.spec_gcd; fold a; fold b; auto.
 intros HH; generalize H1; simpl wf.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto.
 rewrite BigN.spec_0.
 intros HH3; case HH3; fold b.
 rewrite (Zdivide_Zdiv_eq (Zgcd a b) b); auto.
 rewrite HH; auto with zarith.
 assert (F1:= Zgcd_is_gcd a b); inversion F1; auto.
 intros HH1 HH2; apply wf_norm.
 rewrite BigN.spec_mul; intros HH3.
 case (Zmult_integral _ _ HH3).
 generalize HH1; simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto.
 generalize HH2; simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto.
 Qed.

 Theorem spec_mul_norm x y: wf x -> wf y ->
  ([mul_norm x y] == [x] * [y])%Q.
 intros x y Hx Hy; rewrite <- spec_mul; auto.
 unfold mul_norm, mul; generalize Hx Hy; case x; case y; clear Hx Hy.
  intros; apply Qeq_refl.
 intros p1 n p2 Hx Hy.
 match goal with  |- context[BigZ.eq_bool ?X ?Y] => 
   generalize (BigZ.spec_eq_bool X Y); case BigZ.eq_bool
 end; unfold zero, to_Q; repeat rewrite BigZ.spec_0; intros H.
 rewrite BigZ.spec_mul; rewrite H; red; auto.
 assert (F: (0 < BigN.to_Z (BigZ.to_N p2))%Z).
  case (Zle_lt_or_eq _ _ (BigN.spec_pos (BigZ.to_N p2))); auto.
  intros H1; case H; rewrite spec_to_N; rewrite <- H1; ring.
 assert (F1: (0 < BigN.to_Z n)%Z).
  generalize Hy; simpl.
  match goal with  |- context[BigN.eq_bool ?X ?Y] => 
    generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
  end; auto.
  intros _ HH; case HH.
  rewrite BigN.spec_0; generalize (BigN.spec_pos n); auto with zarith.
 set (a := BigN.to_Z (BigZ.to_N p2)).
 set (b := BigN.to_Z n).
 assert (F2: (0 < Zgcd a b )%Z).
   case (Zle_lt_or_eq _ _ (Zgcd_is_pos a b)); intros H3; auto.
   generalize F; fold a; rewrite (Zgcd_inv_0_l _ _ (sym_equal H3)); auto with zarith.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_1; try rewrite BigN.spec_gcd; 
  fold a b; intros H1.
  intros; apply Qeq_refl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_1.
 rewrite BigN.spec_div; rewrite BigN.spec_gcd;
   auto with zarith; fold a b; intros H2.
 red; simpl.
 repeat rewrite BigZ.spec_mul.
 rewrite BigZ.spec_div; simpl; rewrite BigN.spec_gcd; 
   fold a b; auto with zarith.
 rewrite Z2P_correct; auto with zarith.
 rewrite spec_to_N; fold a; fold b.
 rewrite Zmult_1_r; repeat rewrite <- Zmult_assoc.
 rewrite (Zmult_comm (BigZ.to_Z p1)).
 repeat rewrite Zmult_assoc.
 rewrite Zgcd_div_swap; auto with zarith.
 rewrite H2; ring.
 repeat rewrite BigZ.spec_mul.
 rewrite BigZ.spec_div; simpl; rewrite BigN.spec_gcd; 
   fold a b; auto with zarith.
 rewrite BigN.spec_div; simpl; rewrite BigN.spec_gcd; 
   fold a b; auto with zarith.
 intros H2; red; simpl.
 repeat rewrite BigZ.spec_mul.
 rewrite Z2P_correct; auto with zarith.
 rewrite (spec_to_N p2); fold a b.
 rewrite Z2P_correct; auto with zarith.
 repeat rewrite <- Zmult_assoc.
 rewrite (Zmult_comm (BigZ.to_Z p1)).
 repeat rewrite Zmult_assoc.
 rewrite Zgcd_div_swap; auto; try ring.
 case (Zle_lt_or_eq _ _
       (BigN.spec_pos  (n / 
                         BigN.gcd (BigZ.to_N p2) 
                                  n))%bigN);
 rewrite BigN.spec_div; simpl; rewrite BigN.spec_gcd; 
   fold a b; auto with zarith.
 intros H3.
 apply False_ind; generalize F1.
 generalize Hy; simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; auto with zarith.
 intros HH; case HH; fold b.
 rewrite (Zdivide_Zdiv_eq (Zgcd a b) b); auto.
 rewrite <- H3; ring.
 assert (FF:= Zgcd_is_gcd a b); inversion FF; auto.
 intros p1 p2 n Hx Hy.
 match goal with  |- context[BigZ.eq_bool ?X ?Y] => 
   generalize (BigZ.spec_eq_bool X Y); case BigZ.eq_bool
 end; unfold zero, to_Q; repeat rewrite BigZ.spec_0; intros H.
 rewrite BigZ.spec_mul; rewrite H; red; simpl; ring.
 set (a := BigN.to_Z (BigZ.to_N p1)).
 set (b := BigN.to_Z n).
 assert (F: (0 < a)%Z).
  case (Zle_lt_or_eq _ _ (BigN.spec_pos (BigZ.to_N p1))); auto.
  intros H1; case H; rewrite spec_to_N; rewrite <- H1; ring.
 assert (F1: (0 < b)%Z).
  generalize Hx; unfold wf.
  match goal with  |- context[BigN.eq_bool ?X ?Y] => 
    generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
  end; rewrite BigN.spec_0; auto with zarith.
  generalize (BigN.spec_pos n); fold b; auto with zarith.
 assert (F2: (0 < Zgcd a b)%Z).
   case (Zle_lt_or_eq _ _ (Zgcd_is_pos a b)); intros H3; auto.
   generalize F; rewrite (Zgcd_inv_0_l _ _ (sym_equal H3)); auto with zarith.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_1; rewrite BigN.spec_gcd; fold a b; intros H1.
  intros; repeat rewrite BigZ.spec_mul; rewrite Zmult_comm; apply Qeq_refl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_1.
 rewrite BigN.spec_div; rewrite BigN.spec_gcd;
   auto with zarith.
 fold a b; intros H2.
 red; simpl.
 repeat rewrite BigZ.spec_mul.
 rewrite BigZ.spec_div; simpl; rewrite BigN.spec_gcd;
   fold a b; auto with zarith.
 rewrite Z2P_correct; auto with zarith.
 rewrite spec_to_N; fold a b.
 rewrite Zmult_1_r; repeat rewrite <- Zmult_assoc.
 rewrite (Zmult_comm (BigZ.to_Z p2)).
 repeat rewrite Zmult_assoc.
 rewrite Zgcd_div_swap; auto with zarith.
 rewrite H2; ring.
 intros H2.
 red; simpl.
 repeat rewrite BigZ.spec_mul.
 rewrite BigZ.spec_div; simpl; rewrite BigN.spec_gcd; 
   fold a b; auto with zarith.
 rewrite Z2P_correct; auto with zarith.
 rewrite (spec_to_N p1); fold a b.
 case (Zle_lt_or_eq _ _
       (BigN.spec_pos  (n / BigN.gcd (BigZ.to_N p1) n))%bigN); intros F3.
 rewrite Z2P_correct; auto with zarith.
 rewrite BigN.spec_div; simpl; rewrite BigN.spec_gcd; 
   fold a b; auto with zarith.
 repeat rewrite <- Zmult_assoc.
 rewrite (Zmult_comm (BigZ.to_Z p2)).
 repeat rewrite Zmult_assoc.
 rewrite Zgcd_div_swap; auto; try ring.
 apply False_ind; generalize F1.
 rewrite (Zdivide_Zdiv_eq (Zgcd a b) b); auto.
 generalize F3; rewrite BigN.spec_div; rewrite BigN.spec_gcd; fold a b;
   auto with zarith.
 intros HH; rewrite <- HH; auto with zarith.
 assert (FF:= Zgcd_is_gcd a b); inversion FF; auto.
 intros p1 n1 p2 n2 Hn1 Hn2.
 match goal with |- [norm ?X ?Y] == _ =>
  apply Qeq_trans with ([Qq X Y]);
  [apply spec_norm | idtac]
 end; try  apply Qeq_refl.
 rewrite BigN.spec_mul.
 apply Zmult_lt_0_compat.
 generalize Hn1; simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; auto with zarith.
 generalize (BigN.spec_pos n1) (BigN.spec_pos n2); auto with zarith.
 generalize Hn2; simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; auto with zarith.
 generalize (BigN.spec_pos n1) (BigN.spec_pos n2); auto with zarith.
 Qed.

 Theorem spec_mul_normc x y: wf x -> wf y ->
   [[mul_norm x y]] = [[x]] * [[y]].
 intros x y Hx Hy; unfold to_Qc.
 apply trans_equal with (!! ([x] * [y])).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_mul_norm; auto.
 unfold Qcmult, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 apply Qmult_comp; apply Qeq_sym; apply Qred_correct.
 Qed.

 Definition inv (x: t): t := 
  match x with
  | Qz (BigZ.Pos n) => 
    if BigN.eq_bool n BigN.zero then zero else Qq BigZ.one n
  | Qz (BigZ.Neg n) => 
    if BigN.eq_bool n BigN.zero then zero else Qq BigZ.minus_one n
  | Qq (BigZ.Pos n) d => 
    if BigN.eq_bool n BigN.zero then zero else Qq (BigZ.Pos d) n
  | Qq (BigZ.Neg n) d => 
    if BigN.eq_bool n BigN.zero then zero else Qq (BigZ.Neg d) n
  end.


 Theorem wf_inv: forall x, wf x -> wf (inv x).
 intros [ zx | nx dx]; unfold inv, wf; auto.
 case zx; clear zx.
 intros nx.
 repeat match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_0; rewrite BigN.spec_mul.
 intros nx.
 repeat match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_0; rewrite BigN.spec_mul.
 repeat match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_0.
 intros _ HH; case HH.
 intros H1 _.
 case nx; clear nx.
 intros nx.
 repeat match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; simpl; auto.
 intros nx.
 repeat match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; simpl; auto.
 Qed.

 Theorem spec_inv x: wf x ->
   ([inv x] == /[x])%Q.
 intros [ [x | x] _ | [nx | nx] dx]; unfold inv.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H.
  unfold zero, to_Q; rewrite BigZ.spec_0.
 unfold BigZ.to_Z; rewrite H; apply Qeq_refl.
 assert (F: (0 < BigN.to_Z x)%Z).
   case (Zle_lt_or_eq _ _ (BigN.spec_pos x)); auto with zarith.
 unfold to_Q; rewrite BigZ.spec_1.
 red; unfold Qinv; simpl.
 generalize F; case BigN.to_Z; auto with zarith.
 intros p Hp; discriminate Hp.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H.
  unfold zero, to_Q; rewrite BigZ.spec_0.
 unfold BigZ.to_Z; rewrite H; apply Qeq_refl.
 assert (F: (0 < BigN.to_Z x)%Z).
   case (Zle_lt_or_eq _ _ (BigN.spec_pos x)); auto with zarith.
 red; unfold Qinv; simpl.
 generalize F; case BigN.to_Z; simpl; auto with zarith.
 intros p Hp; discriminate Hp.
 simpl wf.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H1.
 intros HH; case HH.
 intros _.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H.
  unfold zero, to_Q; rewrite BigZ.spec_0.
 unfold BigZ.to_Z; rewrite H; apply Qeq_refl.
 assert (F: (0 < BigN.to_Z nx)%Z).
   case (Zle_lt_or_eq _ _ (BigN.spec_pos nx)); auto with zarith.
 red; unfold Qinv; simpl.
 rewrite Z2P_correct; auto with zarith.
 generalize F; case BigN.to_Z; auto with zarith.
 intros p Hp; discriminate Hp.
 generalize (BigN.spec_pos dx); auto with zarith.
 simpl wf.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H1.
 intros HH; case HH.
 intros _.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H.
  unfold zero, to_Q; rewrite BigZ.spec_0.
 unfold BigZ.to_Z; rewrite H; apply Qeq_refl.
 assert (F: (0 < BigN.to_Z nx)%Z).
   case (Zle_lt_or_eq _ _ (BigN.spec_pos nx)); auto with zarith.
 red; unfold Qinv; simpl.
 rewrite Z2P_correct; auto with zarith.
 generalize F; case BigN.to_Z; auto with zarith.
 simpl; intros. 
 match goal with  |- (?X = Zneg ?Y)%Z => 
   replace (Zneg Y) with (Zopp (Zpos Y));
   try rewrite Z2P_correct; auto with zarith
 end.
 rewrite Zpos_mult_morphism; 
   rewrite Z2P_correct; auto with zarith; try ring.
 generalize (BigN.spec_pos dx); auto with zarith.
 intros p Hp; discriminate Hp.
 generalize (BigN.spec_pos dx); auto with zarith.
 Qed.

 Theorem spec_invc x: wf x ->
   [[inv x]] =  /[[x]].
 intros x Hx; unfold to_Qc.
 apply trans_equal with (!! (/[x])).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_inv; auto.
 unfold Qcinv, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 apply Qinv_comp; apply Qeq_sym; apply Qred_correct.
 Qed.


 Definition div x y := mul x (inv y).

 Theorem wf_div x y: wf x -> wf y -> wf (div x y).
 intros x y Hx Hy; unfold div; apply wf_mul; auto.
 apply wf_inv; auto.
 Qed.

 Theorem spec_div x y: wf x -> wf y ->
  ([div x y] == [x] / [y])%Q.
 intros x y Hx Hy; unfold div; rewrite spec_mul; auto.
 unfold Qdiv; apply Qmult_comp.
 apply Qeq_refl.
 apply spec_inv; auto.
 apply wf_inv; auto.
 Qed.

 Theorem spec_divc x y: wf x -> wf y ->
   [[div x y]] = [[x]] / [[y]].
 intros x y Hx Hy; unfold div; rewrite spec_mulc; auto.
 unfold Qcdiv; apply f_equal2 with (f := Qcmult); auto.
 apply spec_invc; auto. 
 apply wf_inv; auto.
 Qed.

 Definition div_norm x y := mul_norm x (inv y).

 Theorem wf_div_norm x y: wf x -> wf y -> wf (div_norm x y).
 intros x y Hx Hy; unfold div_norm; apply wf_mul_norm; auto.
 apply wf_inv; auto.
 Qed.

 Theorem spec_div_norm x y: wf x -> wf y ->
  ([div_norm x y] == [x] / [y])%Q.
 intros x y Hx Hy; unfold div_norm; rewrite spec_mul_norm; auto.
 unfold Qdiv; apply Qmult_comp.
 apply Qeq_refl.
 apply spec_inv; auto.
 apply wf_inv; auto.
 Qed.

 Theorem spec_div_normc x y: wf x -> wf y ->
   [[div_norm x y]] = [[x]] / [[y]].
 intros x y Hx Hy; unfold div_norm; rewrite spec_mul_normc; auto.
 unfold Qcdiv; apply f_equal2 with (f := Qcmult); auto.
 apply spec_invc; auto.
 apply wf_inv; auto.
 Qed.

 Definition square (x: t): t :=
  match x with
  | Qz zx => Qz (BigZ.square zx)
  | Qq nx dx => Qq (BigZ.square nx) (BigN.square dx)
  end.

 Theorem wf_square: forall x, wf x -> wf (square x).
 intros [ zx | nx dx]; unfold square, wf; auto.
 repeat match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_0.
 rewrite BigN.spec_square; intros H1 H2; case H2.
 case (Zmult_integral _ _ H1); auto.
 Qed.

 Theorem spec_square x: wf x -> ([square x] == [x] ^ 2)%Q.
 intros [ x | nx dx]; unfold square.
 intros _.
 red; simpl; rewrite BigZ.spec_square; auto with zarith.
 unfold wf.
 repeat match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_0.
 intros _ HH; case HH.
 intros H1 _.
 red; simpl; rewrite BigZ.spec_square; auto with zarith.
 assert (F: (0 < BigN.to_Z dx)%Z).
   case (Zle_lt_or_eq _ _ (BigN.spec_pos dx)); auto with zarith.
 assert (F1 : (0 < BigN.to_Z (BigN.square dx))%Z).
   rewrite BigN.spec_square; apply Zmult_lt_0_compat;
     auto with zarith.
 rewrite Zpos_mult_morphism.
 repeat rewrite Z2P_correct; auto with zarith.
 rewrite BigN.spec_square; auto with zarith.
 Qed.

 Theorem spec_squarec x: wf x -> [[square x]] =  [[x]]^2.
 intros x Hx; unfold to_Qc.
 apply trans_equal with (!! ([x]^2)).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_square; auto.
 simpl Qcpower.
 replace (!! [x] * 1) with (!![x]); try ring.
 simpl.
 unfold Qcmult, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 apply Qmult_comp; apply Qeq_sym; apply Qred_correct.
 Qed.


 Definition power_pos (x: t) p: t :=
  match x with
  | Qz zx => Qz (BigZ.power_pos zx p)
  | Qq nx dx => Qq (BigZ.power_pos nx p) (BigN.power_pos dx p)
  end.

 Theorem wf_power_pos: forall x p, wf x -> wf (power_pos x p).
 intros [ zx | nx dx] p; unfold power_pos, wf; auto.
 repeat match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_0.
 rewrite BigN.spec_power_pos; simpl.
 intros H1 H2 _.
 case (Zle_lt_or_eq _ _ (BigN.spec_pos dx)); auto with zarith.
 intros H3; generalize (Zpower_pos_pos _ p H3); auto with zarith.
 Qed.

 Theorem spec_power_pos x p: wf x -> ([power_pos x p] == [x] ^ Zpos p)%Q.
 Proof.
 intros [x | nx dx] p; unfold power_pos.
   intros _; unfold power_pos; red; simpl.
   generalize (Qpower_decomp p (BigZ.to_Z x) 1).
   unfold Qeq; simpl.
   rewrite Zpower_pos_1_l; simpl Z2P.
   rewrite Zmult_1_r.
   intros H; rewrite H.
   rewrite BigZ.spec_power_pos; simpl; ring.
 unfold wf.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_0.
 intros _ HH; case HH.
 intros H1 _.
 assert (F1: (0 < BigN.to_Z dx)%Z).
     generalize (BigN.spec_pos dx); auto with zarith.
 assert (F2: (0 < BigN.to_Z dx  ^ ' p)%Z).
  unfold Zpower; apply Zpower_pos_pos; auto.
 unfold power_pos; red; simpl.
 rewrite Z2P_correct; rewrite BigN.spec_power_pos; auto.
 generalize (Qpower_decomp p (BigZ.to_Z nx) 
               (Z2P (BigN.to_Z dx))).
 unfold Qeq; simpl.
 repeat rewrite Z2P_correct; auto.
 unfold Qeq; simpl; intros HH.
 rewrite HH.
 rewrite BigZ.spec_power_pos; simpl; ring.
 Qed.

 Theorem spec_power_posc x p: wf x ->
   [[power_pos x p]] = [[x]] ^ nat_of_P p.
 intros x p Hx; unfold to_Qc.
 apply trans_equal with (!! ([x]^Zpos p)).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_power_pos; auto.
 pattern p; apply Pind; clear p.
 simpl; ring.
 intros p Hrec.
 rewrite nat_of_P_succ_morphism; simpl Qcpower.
 rewrite <- Hrec.
 unfold Qcmult, Q2Qc.
 apply Qc_decomp; intros _ _;
 unfold this.
 apply Qred_complete.
 assert (F: [x] ^ ' Psucc p == [x] *   [x] ^ ' p).
  simpl; generalize Hx; case x; simpl; clear x Hx Hrec.
  intros x _; simpl; repeat rewrite Qpower_decomp; simpl.
  red; simpl; repeat rewrite Zpower_pos_1_l; simpl Z2P.
  rewrite Pplus_one_succ_l.
  rewrite Zpower_pos_is_exp.
  rewrite Zpower_pos_1_r; auto.
  intros nx dx.
  match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
  end; auto; rewrite BigN.spec_0.
  intros _ HH; case HH.
  intros H1 _.
  assert (F1: (0 < BigN.to_Z dx)%Z).
     generalize (BigN.spec_pos dx); auto with zarith.
  simpl; repeat rewrite Qpower_decomp; simpl.
  red; simpl; repeat rewrite Zpower_pos_1_l; simpl Z2P.
  rewrite Pplus_one_succ_l.
  rewrite Zpower_pos_is_exp.
  rewrite Zpower_pos_1_r; auto.
  repeat rewrite Zpos_mult_morphism.
  repeat rewrite Z2P_correct; auto.
  2: apply Zpower_pos_pos; auto.
  2: apply Zpower_pos_pos; auto.
  rewrite Zpower_pos_is_exp.
  rewrite Zpower_pos_1_r; auto.
 rewrite F.
 apply Qmult_comp; apply Qeq_sym; apply Qred_correct.
 Qed.

End Qv.

