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
Require Import QSig.
Require Import QMake_base.

Module Q0 <: QType.

 Import BinInt Zorder.

 (** The notation of a rational number is either an integer x,
     interpreted as itself or a pair (x,y) of an integer x and a natural
     number y interpreted as x/y. The pairs (x,0) and (0,y) are all
     interpreted as 0. *)

 Definition t := q_type.

 (** Specification with respect to [QArith] *) 

 Open Local Scope Q_scope.

 Definition of_Z x: t := Qz (BigZ.of_Z x).

 Definition of_Q q: t := 
 match q with x # y =>
  Qq (BigZ.of_Z x) (BigN.of_N (Npos y))
 end.

 Definition to_Q (q: t) := 
 match q with 
  Qz x => BigZ.to_Z x # 1
 |Qq x y => if BigN.eq_bool y BigN.zero then 0
            else BigZ.to_Z x # Z2P (BigN.to_Z y)
 end.

 Notation "[ x ]" := (to_Q x).

 Theorem strong_spec_of_Q: forall q: Q, [of_Q q] = q.
 Proof.
 intros (x,y); simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
  generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_0.
   rewrite BigN.spec_of_pos; intros HH; discriminate HH.
 rewrite BigZ.spec_of_Z; simpl.
 rewrite (BigN.spec_of_pos); auto.
 Qed.

 Theorem spec_of_Q: forall q: Q, [of_Q q] == q.
 Proof.
 intros; rewrite strong_spec_of_Q; red; auto.
 Qed.

 Definition eq x y := [x] == [y].

 Definition zero: t := Qz BigZ.zero.
 Definition one: t := Qz BigZ.one.
 Definition minus_one: t := Qz BigZ.minus_one.

 Lemma spec_0: [zero] == 0.
 Proof.
 reflexivity.
 Qed.

 Lemma spec_1: [one] == 1.
 Proof.
 reflexivity.
 Qed.

 Lemma spec_m1: [minus_one] == -(1).
 Proof.
 reflexivity.
 Qed.

 Definition opp (x: t): t :=
  match x with
  | Qz zx => Qz (BigZ.opp zx)
  | Qq nx dx => Qq (BigZ.opp nx) dx
  end.

 Theorem strong_spec_opp: forall q, [opp q] = -[q].
 Proof.
 intros [z | x y]; simpl.
 rewrite BigZ.spec_opp; auto.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
  generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_0.
 rewrite BigZ.spec_opp; auto.
 Qed.

 Theorem spec_opp : forall q, [opp q] == -[q].
 Proof.
 intros; rewrite strong_spec_opp; red; auto.
 Qed.

 Definition compare (x y: t) :=
  match x, y with
  | Qz zx, Qz zy => BigZ.compare zx zy
  | Qz zx, Qq ny dy => 
    if BigN.eq_bool dy BigN.zero then BigZ.compare zx BigZ.zero
    else BigZ.compare (BigZ.mul zx (BigZ.Pos dy)) ny
  | Qq nx dx, Qz zy => 
    if BigN.eq_bool dx BigN.zero then BigZ.compare BigZ.zero zy 
    else BigZ.compare nx (BigZ.mul zy (BigZ.Pos dx))
  | Qq nx dx, Qq ny dy =>
    match BigN.eq_bool dx BigN.zero, BigN.eq_bool dy BigN.zero with
    | true, true => Eq
    | true, false => BigZ.compare BigZ.zero ny
    | false, true => BigZ.compare nx BigZ.zero
    | false, false => BigZ.compare (BigZ.mul nx (BigZ.Pos dy)) (BigZ.mul ny (BigZ.Pos dx))
    end
  end.

 Theorem spec_compare: forall q1 q2, (compare q1 q2) = ([q1] ?= [q2]).
 Proof.
 intros [z1 | x1 y1] [z2 | x2 y2]; 
   unfold Qcompare, compare, to_Q, Qnum, Qden.
 repeat rewrite Zmult_1_r.
 generalize (BigZ.spec_compare z1 z2); case BigZ.compare; intros H; auto.
 rewrite H; rewrite Zcompare_refl; auto.
 rewrite Zmult_1_r.
 generalize (BigN.spec_eq_bool y2 BigN.zero);
   case BigN.eq_bool; rewrite BigN.spec_0; intros HH.
 rewrite Zmult_1_r; generalize (BigZ.spec_compare z1 BigZ.zero);
  case BigZ.compare; auto.
 rewrite BigZ.spec_0; intros HH1; rewrite HH1; rewrite Zcompare_refl; auto.
 rewrite Z2P_correct; auto with zarith.
  2: generalize (BigN.spec_pos y2); auto with zarith.
 generalize (BigZ.spec_compare (z1 * BigZ.Pos y2) x2)%bigZ; case BigZ.compare;
   rewrite BigZ.spec_mul; simpl; intros H; apply sym_equal; auto.
 rewrite H; rewrite Zcompare_refl; auto.
 generalize (BigN.spec_eq_bool y1 BigN.zero);
   case BigN.eq_bool; rewrite BigN.spec_0; intros HH.
 rewrite Zmult_0_l; rewrite Zmult_1_r.
 generalize (BigZ.spec_compare BigZ.zero z2);
  case BigZ.compare; auto.
 rewrite BigZ.spec_0; intros HH1; rewrite <- HH1; rewrite Zcompare_refl; auto.
 rewrite Z2P_correct; auto with zarith.
  2: generalize (BigN.spec_pos y1); auto with zarith.
 rewrite Zmult_1_r.
 generalize (BigZ.spec_compare x1 (z2 * BigZ.Pos y1))%bigZ; case BigZ.compare;
   rewrite BigZ.spec_mul; simpl; intros H; apply sym_equal; auto.
 rewrite H; rewrite Zcompare_refl; auto.
 generalize (BigN.spec_eq_bool y1 BigN.zero);
   case BigN.eq_bool; rewrite BigN.spec_0; intros HH.
 generalize (BigN.spec_eq_bool y2 BigN.zero);
   case BigN.eq_bool; rewrite BigN.spec_0; intros HH1.
 rewrite Zcompare_refl; auto.
 rewrite Zmult_0_l; rewrite Zmult_1_r.
 generalize (BigZ.spec_compare BigZ.zero x2);
  case BigZ.compare; auto.
 rewrite BigZ.spec_0; intros HH2; rewrite <- HH2; rewrite Zcompare_refl; auto.
 generalize (BigN.spec_eq_bool y2 BigN.zero);
   case BigN.eq_bool; rewrite BigN.spec_0; intros HH1.
 rewrite Zmult_0_l; rewrite Zmult_1_r.
 generalize (BigZ.spec_compare x1 BigZ.zero)%bigZ; case BigZ.compare;
   auto; rewrite BigZ.spec_0.
 intros HH2; rewrite <- HH2; rewrite Zcompare_refl; auto.
 repeat rewrite Z2P_correct.
  2: generalize (BigN.spec_pos y1); auto with zarith.
  2: generalize (BigN.spec_pos y2); auto with zarith.
 generalize (BigZ.spec_compare (x1 * BigZ.Pos y2) 
                               (x2 * BigZ.Pos y1))%bigZ; case BigZ.compare;
   repeat rewrite BigZ.spec_mul; simpl; intros H; apply sym_equal; auto.
 rewrite H; rewrite Zcompare_refl; auto.
 Qed.

 Definition lt n m := compare n m = Lt.
 Definition le n m := compare n m <> Gt.
 Definition min n m := match compare n m with Gt => m | _ => n end.
 Definition max n m := match compare n m with Lt => m | _ => n end.

(* Je pense que cette fonction normalise bien ... *)
 Definition norm n d: t :=
  let gcd := BigN.gcd (BigZ.to_N n) d in 
  match BigN.compare BigN.one gcd with
  | Lt => 
    let n := BigZ.div n (BigZ.Pos gcd) in
    let d := BigN.div d gcd in
    match BigN.compare d BigN.one with
    | Gt => Qq n d
    | Eq => Qz n
    | Lt => zero
    end
  | Eq => Qq n d
  | Gt => zero (* gcd = 0 => both numbers are 0 *)
  end.

 Theorem spec_norm: forall n q, [norm n q] == [Qq n q].
 Proof.
 intros p q; unfold norm.
 assert (Hp := BigN.spec_pos (BigZ.to_N p)).
 match goal with  |- context[BigN.compare ?X ?Y] => 
   generalize (BigN.spec_compare X Y); case BigN.compare
 end; auto; rewrite BigN.spec_1; rewrite BigN.spec_gcd; intros H1.
   apply Qeq_refl.
 generalize (BigN.spec_pos (q / BigN.gcd (BigZ.to_N p) q)%bigN).
 match goal with  |- context[BigN.compare ?X ?Y] => 
   generalize (BigN.spec_compare X Y); case BigN.compare
 end; auto; rewrite BigN.spec_1; rewrite BigN.spec_div; 
   rewrite BigN.spec_gcd; auto with zarith; intros H2 HH.
 red; simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_0; intros H3; simpl;
  rewrite BigZ.spec_div; simpl; rewrite BigN.spec_gcd;
  auto with zarith.
 generalize H2; rewrite H3; 
   rewrite Zdiv_0_l; auto with zarith.
 generalize H1 H2 H3 (BigN.spec_pos q); clear H1 H2 H3.
 rewrite spec_to_N.
 set (a := (BigN.to_Z (BigZ.to_N p))).
 set (b := (BigN.to_Z q)).
 intros H1 H2 H3 H4; rewrite Z2P_correct; auto with zarith.
 rewrite Zgcd_div_swap; auto with zarith.
 rewrite H2; ring.
 red; simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_0; intros H3; simpl.
 case H3.
 generalize H1 H2 H3 HH; clear H1 H2 H3 HH.
 set (a := (BigN.to_Z (BigZ.to_N p))).
 set (b := (BigN.to_Z q)).
 intros H1 H2 H3 HH.
  rewrite (Zdivide_Zdiv_eq (Zgcd a b) b); auto with zarith.
 case (Zle_lt_or_eq _ _ HH); auto with zarith.
 intros HH1; rewrite <- HH1; ring.
 generalize (Zgcd_is_gcd a b); intros HH1; inversion HH1; auto.
 red; simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_0; rewrite BigN.spec_div;
   rewrite BigN.spec_gcd; auto with zarith; intros H3.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_0; intros H4.
 case H3; rewrite H4;  rewrite Zdiv_0_l; auto with zarith.
 simpl.
 assert (FF := BigN.spec_pos q).
 rewrite Z2P_correct; auto with zarith.
 rewrite <- BigN.spec_gcd; rewrite <- BigN.spec_div; auto with zarith.
 rewrite Z2P_correct; auto with zarith.
 rewrite BigN.spec_div; rewrite BigN.spec_gcd; auto with zarith.
 simpl; rewrite BigZ.spec_div; simpl.
 rewrite BigN.spec_gcd; auto with zarith.
 generalize H1 H2 H3 H4 HH FF; clear H1 H2 H3 H4 HH FF.
 set (a := (BigN.to_Z (BigZ.to_N p))).
 set (b := (BigN.to_Z q)).
 intros H1 H2 H3 H4 HH FF.
 rewrite spec_to_N; fold a.
 rewrite Zgcd_div_swap; auto with zarith.
 rewrite BigN.spec_gcd; auto with zarith.
 rewrite BigN.spec_div; 
   rewrite BigN.spec_gcd; auto with zarith.
 rewrite BigN.spec_gcd; auto with zarith.
 case (Zle_lt_or_eq _ _ 
   (BigN.spec_pos (BigN.gcd (BigZ.to_N p) q)));
  rewrite BigN.spec_gcd; auto with zarith.
 intros; apply False_ind; auto with zarith.
 intros HH2; assert (FF1 := Zgcd_inv_0_l _ _ (sym_equal HH2)).
 assert (FF2 := Zgcd_inv_0_l _ _ (sym_equal HH2)).
 red; simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_0; intros H2; simpl.
 rewrite spec_to_N.
 rewrite FF2; ring.
 Qed.

   
 Definition add (x y: t): t :=
  match x with
  | Qz zx =>
    match y with
    | Qz zy => Qz (BigZ.add zx zy)
    | Qq ny dy => 
      if BigN.eq_bool dy BigN.zero then x 
      else Qq (BigZ.add (BigZ.mul zx (BigZ.Pos dy)) ny) dy
    end
  | Qq nx dx =>
    if BigN.eq_bool dx BigN.zero then y 
    else match y with
    | Qz zy => Qq (BigZ.add nx (BigZ.mul zy (BigZ.Pos dx))) dx
    | Qq ny dy =>
      if BigN.eq_bool dy BigN.zero then x
      else
       let n := BigZ.add (BigZ.mul nx (BigZ.Pos dy)) (BigZ.mul ny (BigZ.Pos dx)) in
       let d := BigN.mul dx dy in
       Qq n d
    end
  end.

 Theorem spec_add : forall x y, [add x y] == [x] + [y].
 Proof.
 intros [x | nx dx] [y | ny dy]; unfold Qplus; simpl.
 rewrite BigZ.spec_add; repeat rewrite Zmult_1_r; auto.
  intros; apply Qeq_refl; auto.
 assert (F1:= BigN.spec_pos dy).
 rewrite Zmult_1_r; red; simpl.
 generalize (BigN.spec_eq_bool dy BigN.zero);
   case BigN.eq_bool;
   rewrite BigN.spec_0; intros HH; simpl; try ring.
 generalize (BigN.spec_eq_bool dy BigN.zero);
   case BigN.eq_bool;
   rewrite BigN.spec_0; intros HH1; simpl; try ring.
 case HH; auto.
 rewrite Z2P_correct; auto with zarith.
 rewrite BigZ.spec_add; rewrite BigZ.spec_mul; simpl; auto.
 generalize (BigN.spec_eq_bool dx BigN.zero);
   case BigN.eq_bool;
   rewrite BigN.spec_0; intros HH; simpl; try ring.
 rewrite Zmult_1_r; apply Qeq_refl.
 generalize (BigN.spec_eq_bool dx BigN.zero);
   case BigN.eq_bool;
   rewrite BigN.spec_0; intros HH1; simpl; try ring.
 case HH; auto.
 rewrite Z2P_correct; auto with zarith.
 rewrite BigZ.spec_add; rewrite BigZ.spec_mul; simpl; auto.
 rewrite Zmult_1_r; rewrite Pmult_1_r.
 apply Qeq_refl.
 assert (F1:= BigN.spec_pos dx); auto with zarith.
 generalize (BigN.spec_eq_bool dx BigN.zero);
   case BigN.eq_bool; rewrite BigN.spec_0; intros HH.
 generalize (BigN.spec_eq_bool dy BigN.zero);
   case BigN.eq_bool; rewrite BigN.spec_0; intros HH1.
 simpl.
 generalize (BigN.spec_eq_bool dy BigN.zero);
   case BigN.eq_bool; rewrite BigN.spec_0; intros HH2.
 apply Qeq_refl.
 case HH2; auto.
 simpl.
 generalize (BigN.spec_eq_bool dy BigN.zero);
   case BigN.eq_bool; rewrite BigN.spec_0; intros HH2.
 case HH2; auto.
 case HH1; auto.
 rewrite Zmult_1_r; apply Qeq_refl.
 generalize (BigN.spec_eq_bool dy BigN.zero);
   case BigN.eq_bool; rewrite BigN.spec_0; intros HH1.
 simpl.
 generalize (BigN.spec_eq_bool dx BigN.zero);
   case BigN.eq_bool; rewrite BigN.spec_0; intros HH2.
 case HH; auto.
 rewrite Zmult_1_r; rewrite Zplus_0_r; rewrite Pmult_1_r.
 apply Qeq_refl.
 simpl.
 generalize (BigN.spec_eq_bool (dx * dy)%bigN BigN.zero);
   case BigN.eq_bool; rewrite BigN.spec_mul;
   rewrite BigN.spec_0; intros HH2.
 (case (Zmult_integral _ _ HH2); intros HH3);
  [case HH| case HH1]; auto.
 rewrite BigZ.spec_add; repeat rewrite BigZ.spec_mul; simpl.
 assert (Fx: (0 < BigN.to_Z dx)%Z).
   generalize (BigN.spec_pos dx); auto with zarith.
 assert (Fy: (0 < BigN.to_Z dy)%Z).
   generalize (BigN.spec_pos dy); auto with zarith.
 red; simpl; rewrite Zpos_mult_morphism.
 repeat rewrite Z2P_correct; auto with zarith.
 apply Zmult_lt_0_compat; auto.
 Qed.

 Definition add_norm (x y: t): t :=
  match x with
  | Qz zx =>
    match y with
    | Qz zy => Qz (BigZ.add zx zy)
    | Qq ny dy =>  
      if BigN.eq_bool dy BigN.zero then x 
      else norm (BigZ.add (BigZ.mul zx (BigZ.Pos dy)) ny) dy
    end
  | Qq nx dx =>
    if BigN.eq_bool dx BigN.zero then y 
    else match y with
    | Qz zy => norm (BigZ.add nx (BigZ.mul zy (BigZ.Pos dx))) dx
    | Qq ny dy =>
      if BigN.eq_bool dy BigN.zero then x
      else
       let n := BigZ.add (BigZ.mul nx (BigZ.Pos dy)) (BigZ.mul ny (BigZ.Pos dx)) in
       let d := BigN.mul dx dy in
       norm n d
    end
  end.

 Theorem spec_add_norm : forall x y, [add_norm x y] == [x] + [y].
 Proof.
 intros x y; rewrite <- spec_add; auto.
 case x; case y; clear x y; unfold add_norm, add.
  intros; apply Qeq_refl.
 intros p1 n p2.
 generalize (BigN.spec_eq_bool n BigN.zero);
   case BigN.eq_bool; rewrite BigN.spec_0; intros HH.
 apply Qeq_refl.
 match goal with |- [norm ?X ?Y] == _ =>
  apply Qeq_trans with ([Qq X Y]);
  [apply spec_norm | idtac]
 end.
 simpl.
 generalize (BigN.spec_eq_bool n BigN.zero);
   case BigN.eq_bool; rewrite BigN.spec_0; intros HH1.
 apply Qeq_refl.
 apply Qeq_refl.
 intros p1 p2 n.
 generalize (BigN.spec_eq_bool n BigN.zero);
   case BigN.eq_bool; rewrite BigN.spec_0; intros HH.
 apply Qeq_refl.
 match goal with |- [norm ?X ?Y] == _ =>
  apply Qeq_trans with ([Qq X Y]);
  [apply spec_norm | idtac]
 end.
 apply Qeq_refl.
 intros p1 q1 p2 q2.
 generalize (BigN.spec_eq_bool q2 BigN.zero);
   case BigN.eq_bool; rewrite BigN.spec_0; intros HH1.
 apply Qeq_refl.
 generalize (BigN.spec_eq_bool q1 BigN.zero);
   case BigN.eq_bool; rewrite BigN.spec_0; intros HH2.
 apply Qeq_refl.
 match goal with |- [norm ?X ?Y] == _ =>
  apply Qeq_trans with ([Qq X Y]);
  [apply spec_norm | idtac]
 end.
 apply Qeq_refl.
 Qed.

 Definition sub x y := add x (opp y).

 Theorem spec_sub : forall x y, [sub x y] == [x] - [y].
 Proof.
 intros x y; unfold sub; rewrite spec_add; auto.
 rewrite spec_opp; ring.
 Qed.

 Definition sub_norm x y := add_norm x (opp y).

 Theorem spec_sub_norm : forall x y, [sub_norm x y] == [x] - [y].
 Proof.
 intros x y; unfold sub_norm; rewrite spec_add_norm; auto.
 rewrite spec_opp; ring.
 Qed.

 Definition mul (x y: t): t :=
  match x, y with
  | Qz zx, Qz zy => Qz (BigZ.mul zx zy)
  | Qz zx, Qq ny dy => Qq (BigZ.mul zx ny) dy
  | Qq nx dx, Qz zy => Qq (BigZ.mul nx zy) dx
  | Qq nx dx, Qq ny dy => Qq (BigZ.mul nx ny) (BigN.mul dx dy)
  end.

 Theorem spec_mul : forall x y, [mul x y] == [x] * [y].
 Proof.
 intros [x | nx dx] [y | ny dy]; unfold Qmult; simpl.
 rewrite BigZ.spec_mul; repeat rewrite Zmult_1_r; auto.
  intros; apply Qeq_refl; auto.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end;  rewrite BigN.spec_0; intros HH1.
 red; simpl; ring.
 rewrite BigZ.spec_mul; apply Qeq_refl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros HH1.
 red; simpl; ring.
 rewrite BigZ.spec_mul; rewrite Pmult_1_r.
 apply Qeq_refl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0;  rewrite BigN.spec_mul;
      intros HH1.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros HH2.
 red; simpl; auto.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros HH3.
 red; simpl; ring.
 case (Zmult_integral _ _ HH1); intros HH.
   case HH2; auto.
   case HH3; auto.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros HH2.
 case HH1; rewrite HH2; ring.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros HH3.
 case HH1; rewrite HH3; ring.
 rewrite BigZ.spec_mul.
 assert (tmp: 
  (forall a b, 0 < a -> 0 < b -> Z2P (a * b) = (Z2P a * Z2P b)%positive)%Z).
  intros [|a|a] [|b|b]; simpl; auto; intros; apply False_ind; auto with zarith.
 rewrite tmp; auto.
 apply Qeq_refl.
  generalize (BigN.spec_pos dx); auto with zarith.
  generalize (BigN.spec_pos dy); auto with zarith.
 Qed.

Definition mul_norm (x y: t): t := 
 match x, y with
 | Qz zx, Qz zy => Qz (BigZ.mul zx zy)
 | Qz zx, Qq ny dy =>
   if BigZ.eq_bool zx BigZ.zero then zero
   else	
     let gcd := BigN.gcd (BigZ.to_N zx) dy in
     match BigN.compare gcd BigN.one with
       Gt => 
       let zx := BigZ.div zx (BigZ.Pos gcd) in
       let d := BigN.div dy gcd in
       if BigN.eq_bool d BigN.one then Qz (BigZ.mul zx ny)
       else Qq (BigZ.mul zx ny) d
      | _  => Qq (BigZ.mul zx ny) dy
     end
 | Qq nx dx, Qz zy =>   
   if BigZ.eq_bool zy BigZ.zero then zero
   else	
     let gcd := BigN.gcd (BigZ.to_N zy) dx in
     match BigN.compare gcd BigN.one with
       Gt => 
       let zy := BigZ.div zy (BigZ.Pos gcd) in
       let d := BigN.div dx gcd in
       if BigN.eq_bool d BigN.one then Qz (BigZ.mul zy nx)
       else Qq (BigZ.mul zy nx) d
     | _ =>  Qq (BigZ.mul zy nx) dx
     end
 | Qq nx dx, Qq ny dy => 
     let (nx, dy) := 
       let gcd := BigN.gcd (BigZ.to_N nx) dy in
       match BigN.compare gcd BigN.one with 
        Gt => (BigZ.div nx (BigZ.Pos gcd), BigN.div dy gcd)
       | _ => (nx, dy)
       end in
     let (ny, dx) := 
       let gcd := BigN.gcd (BigZ.to_N ny) dx in
       match BigN.compare gcd BigN.one with 
        Gt =>  (BigZ.div ny (BigZ.Pos gcd), BigN.div dx gcd) 
       | _ =>  (ny, dx)
       end in 
     let d := (BigN.mul dx dy) in
     if BigN.eq_bool d BigN.one then Qz (BigZ.mul ny nx) 
     else Qq (BigZ.mul ny nx) d
 end.

 Theorem spec_mul_norm : forall x y, [mul_norm x y] == [x] * [y].
 Proof.
 intros x y; rewrite <- spec_mul; auto.
 unfold mul_norm, mul; case x; case y; clear x y.
  intros; apply Qeq_refl.
 intros p1 n p2.
 set (a := BigN.to_Z (BigZ.to_N p2)).
 set (b := BigN.to_Z n).
 match goal with  |- context[BigZ.eq_bool ?X ?Y] => 
   generalize (BigZ.spec_eq_bool X Y); case BigZ.eq_bool
 end; unfold zero, to_Q; repeat rewrite BigZ.spec_0; intros H.
 case BigN.eq_bool; try apply Qeq_refl.
 rewrite BigZ.spec_mul; rewrite H.
 red; simpl; ring.
 assert (F: (0 < a)%Z).
  case (Zle_lt_or_eq _ _ (BigN.spec_pos (BigZ.to_N p2))); auto.
  intros H1; case H; rewrite spec_to_N; rewrite <- H1; ring.
 match goal with  |- context[BigN.compare ?X ?Y] => 
   generalize (BigN.spec_compare X Y); case BigN.compare
 end; rewrite BigN.spec_1; rewrite BigN.spec_gcd;
      fold a b; intros H1.
 apply Qeq_refl.
 apply Qeq_refl.
 assert (F0 : (0 < (Zgcd a b))%Z).
   apply Zlt_trans with 1%Z.
   red; auto.
   apply Zgt_lt; auto.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_1; rewrite BigN.spec_div;
 rewrite BigN.spec_gcd; auto with zarith; 
 fold a b; intros H2.
 assert (F1: b = Zgcd a b).
   pattern b at 1; rewrite (Zdivide_Zdiv_eq (Zgcd a b) b);
   auto with zarith.
   rewrite H2; ring.
   assert (FF := Zgcd_is_gcd a b); inversion FF; auto.
 assert (F2: (0 < b)%Z).
   rewrite F1; auto.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; fold b; intros H3.
 rewrite H3 in F2; discriminate F2.
 rewrite BigZ.spec_mul.
 rewrite BigZ.spec_div; simpl; rewrite BigN.spec_gcd; 
  fold a b; auto with zarith.
 rewrite BigZ.spec_mul.
 red; simpl; rewrite Z2P_correct; auto.
 rewrite Zmult_1_r; rewrite spec_to_N; fold a b.
 repeat rewrite <- Zmult_assoc.
 rewrite (Zmult_comm (BigZ.to_Z p1)).
 repeat rewrite Zmult_assoc.
 rewrite Zgcd_div_swap; auto with zarith.
 rewrite H2; ring.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; rewrite BigN.spec_div;
 rewrite BigN.spec_gcd; fold a b; auto; intros H3.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H4.
 apply Qeq_refl.
 case H4; fold b.
 rewrite (Zdivide_Zdiv_eq (Zgcd a b) b); auto.
 rewrite H3; ring.
 assert (FF := Zgcd_is_gcd a b); inversion FF; auto.
 simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; fold b; intros H4.
 case H3; rewrite H4; rewrite Zdiv_0_l; auto.
 rewrite BigZ.spec_mul; rewrite BigZ.spec_div; simpl;
  rewrite BigN.spec_gcd; fold a b; auto with zarith.
 assert (F1: (0 < b)%Z).
   case (Zle_lt_or_eq _ _ (BigN.spec_pos n)); fold b; auto with zarith.
 red; simpl.
 rewrite BigZ.spec_mul.
 repeat rewrite Z2P_correct; auto.
 rewrite spec_to_N; fold a.
 repeat rewrite <- Zmult_assoc.
 rewrite (Zmult_comm (BigZ.to_Z p1)).
 repeat rewrite Zmult_assoc.
 rewrite Zgcd_div_swap; auto with zarith.
 ring.
 apply Zgcd_div_pos; auto.
 intros p1 p2 n.
 set (a := BigN.to_Z (BigZ.to_N p1)).
 set (b := BigN.to_Z n).
 match goal with  |- context[BigZ.eq_bool ?X ?Y] => 
   generalize (BigZ.spec_eq_bool X Y); case BigZ.eq_bool
 end; unfold zero, to_Q; repeat rewrite BigZ.spec_0; intros H.
 case BigN.eq_bool; try apply Qeq_refl.
 rewrite BigZ.spec_mul; rewrite H.
 red; simpl; ring.
 assert (F: (0 < a)%Z).
  case (Zle_lt_or_eq _ _ (BigN.spec_pos (BigZ.to_N p1))); auto.
  intros H1; case H; rewrite spec_to_N; rewrite <- H1; ring.
 match goal with  |- context[BigN.compare ?X ?Y] => 
   generalize (BigN.spec_compare X Y); case BigN.compare
 end; rewrite BigN.spec_1; rewrite BigN.spec_gcd;
      fold a b; intros H1.
 repeat rewrite BigZ.spec_mul; rewrite Zmult_comm.
 apply Qeq_refl.
 repeat rewrite BigZ.spec_mul; rewrite Zmult_comm.
 apply Qeq_refl.
 assert (F0 : (0 < (Zgcd a b))%Z).
   apply Zlt_trans with 1%Z.
   red; auto.
   apply Zgt_lt; auto.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_1; rewrite BigN.spec_div;
 rewrite BigN.spec_gcd; auto with zarith; 
 fold a b; intros H2.
 assert (F1: b = Zgcd a b).
   pattern b at 1; rewrite (Zdivide_Zdiv_eq (Zgcd a b) b);
   auto with zarith.
   rewrite H2; ring.
   assert (FF := Zgcd_is_gcd a b); inversion FF; auto.
 assert (F2: (0 < b)%Z).
   rewrite F1; auto.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; fold b; intros H3.
 rewrite H3 in F2; discriminate F2.
 rewrite BigZ.spec_mul.
 rewrite BigZ.spec_div; simpl; rewrite BigN.spec_gcd; 
  fold a b; auto with zarith.
 rewrite BigZ.spec_mul.
 red; simpl; rewrite Z2P_correct; auto.
 rewrite Zmult_1_r; rewrite spec_to_N; fold a b.
 repeat rewrite <- Zmult_assoc.
 rewrite (Zmult_comm (BigZ.to_Z p2)).
 repeat rewrite Zmult_assoc.
 rewrite Zgcd_div_swap; auto with zarith.
 rewrite H2; ring.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; rewrite BigN.spec_div;
 rewrite BigN.spec_gcd; fold a b; auto; intros H3.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H4.
 apply Qeq_refl.
 case H4; fold b.
 rewrite (Zdivide_Zdiv_eq (Zgcd a b) b); auto.
 rewrite H3; ring.
 assert (FF := Zgcd_is_gcd a b); inversion FF; auto.
 simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; fold b; intros H4.
 case H3; rewrite H4; rewrite Zdiv_0_l; auto.
 rewrite BigZ.spec_mul; rewrite BigZ.spec_div; simpl;
  rewrite BigN.spec_gcd; fold a b; auto with zarith.
 assert (F1: (0 < b)%Z).
   case (Zle_lt_or_eq _ _ (BigN.spec_pos n)); fold b; auto with zarith.
 red; simpl.
 rewrite BigZ.spec_mul.
 repeat rewrite Z2P_correct; auto.
 rewrite spec_to_N; fold a.
 repeat rewrite <- Zmult_assoc.
 rewrite (Zmult_comm (BigZ.to_Z p2)).
 repeat rewrite Zmult_assoc.
 rewrite Zgcd_div_swap; auto with zarith.
 ring.
 apply Zgcd_div_pos; auto.
 set (f := fun p t =>
        match (BigN.gcd (BigZ.to_N p) t ?= BigN.one)%bigN with
       | Eq => (p, t)
       | Lt => (p, t)
       | Gt =>
         ((p / BigZ.Pos (BigN.gcd (BigZ.to_N p) t))%bigZ,
           (t / BigN.gcd (BigZ.to_N p) t)%bigN)
       end).
 assert (F: forall p t,
   let (n, d) := f p t in [Qq p t] == [Qq n d]).
 intros p t1; unfold f.
 match goal with  |- context[BigN.compare ?X ?Y] => 
   generalize (BigN.spec_compare X Y); case BigN.compare
 end; rewrite BigN.spec_1; rewrite BigN.spec_gcd; intros H1.
 apply Qeq_refl.
 apply Qeq_refl.
 set (a := BigN.to_Z (BigZ.to_N p)).
 set (b := BigN.to_Z t1).
 fold a b in H1.
 assert (F0 : (0 < (Zgcd a b))%Z).
   apply Zlt_trans with 1%Z.
   red; auto.
   apply Zgt_lt; auto.
 red; simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; fold b; intros HH1.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; fold b; intros HH2.
 simpl; ring.
 case HH2.
 rewrite BigN.spec_div; rewrite BigN.spec_gcd; fold a b; auto.
 rewrite HH1; rewrite Zdiv_0_l; auto.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0;
   rewrite BigN.spec_div; rewrite BigN.spec_gcd; fold a b; auto;
   intros HH2.
 case HH1.
 rewrite (Zdivide_Zdiv_eq (Zgcd a b) b); auto.
 rewrite HH2; ring.
 assert (FF := Zgcd_is_gcd a b); inversion FF; auto.
 simpl.
 rewrite BigZ.spec_div; simpl; rewrite BigN.spec_gcd; fold a b; auto with zarith.
 assert (F1: (0 < b)%Z).
    case (Zle_lt_or_eq _ _ (BigN.spec_pos t1)); fold b; auto with zarith.
    intros HH; case HH1; auto.
 repeat rewrite Z2P_correct; auto.
 rewrite spec_to_N; fold a.
 rewrite Zgcd_div_swap; auto.
 apply Zgcd_div_pos; auto.
 intros HH; rewrite HH in F0; discriminate F0.
 intros p1 n1 p2 n2.
 change ([let (nx , dy) := f p2 n1 in
         let (ny, dx) := f p1 n2 in
  if BigN.eq_bool (dx * dy)%bigN BigN.one
   then Qz (ny * nx)
  else Qq (ny * nx) (dx * dy)] == [Qq (p2 * p1) (n2 * n1)]).
  generalize (F p2 n1) (F p1 n2).
 case f; case f.
 intros u1 u2 v1 v2 Hu1 Hv1.
 apply Qeq_trans with [mul (Qq p2 n1) (Qq p1 n2)].
 rewrite spec_mul; rewrite Hu1; rewrite Hv1.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_1; rewrite BigN.spec_mul; intros HH1.
 assert (F1: BigN.to_Z u2 = 1%Z).
  case (Zmult_1_inversion_l _ _ HH1); auto.
  generalize (BigN.spec_pos u2); auto with zarith.
 assert (F2: BigN.to_Z v2 = 1%Z).
  rewrite Zmult_comm in HH1.
  case (Zmult_1_inversion_l _ _ HH1); auto.
  generalize (BigN.spec_pos v2); auto with zarith.
 red; simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H1.
 rewrite H1 in F2; discriminate F2.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H2.
 rewrite H2 in F1; discriminate F1.
 simpl; rewrite BigZ.spec_mul.
 rewrite F1; rewrite F2; simpl; ring.
 rewrite Qmult_comm; rewrite <- spec_mul.
 apply Qeq_refl.
 red; simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; rewrite BigN.spec_mul;
 rewrite Zmult_comm; intros H1.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; rewrite BigN.spec_mul; intros H2; auto.
 case H2; auto.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; rewrite BigN.spec_mul; intros H2; auto.
 case H1; auto.
 Qed.


Definition inv (x: t): t := 
 match x with
 | Qz (BigZ.Pos n) => Qq BigZ.one n
 | Qz (BigZ.Neg n) => Qq BigZ.minus_one n
 | Qq (BigZ.Pos n) d => Qq (BigZ.Pos d) n
 | Qq (BigZ.Neg n) d => Qq (BigZ.Neg d) n
 end.

 Theorem spec_inv : forall x, [inv x] == /[x].
 Proof.
 intros [ [x | x] | [nx | nx] dx]; unfold inv, Qinv; simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H1; auto.
 rewrite H1; apply Qeq_refl.
 generalize H1 (BigN.spec_pos x); case (BigN.to_Z x); auto.
 intros HH; case HH; auto.
 intros; red; simpl; auto.
 intros p _ HH; case HH; auto.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H1; auto.
 rewrite H1; apply Qeq_refl.
 generalize H1 (BigN.spec_pos x); case (BigN.to_Z x); simpl;
   auto.
 intros HH; case HH; auto.
 intros; red; simpl; auto.
 intros p _ HH; case HH; auto.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H1; auto.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H2; simpl; auto.
 apply Qeq_refl.
 rewrite H1; apply Qeq_refl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H2; simpl; auto.
 rewrite H2; red; simpl; auto.
 generalize H1 (BigN.spec_pos nx); case (BigN.to_Z nx); simpl;
   auto.
 intros HH; case HH; auto.
 intros; red; simpl.
 rewrite Zpos_mult_morphism.
 rewrite Z2P_correct; auto.
 generalize (BigN.spec_pos dx); auto with zarith.
 intros p _ HH; case HH; auto.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H1; auto.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H2; simpl; auto.
 apply Qeq_refl.
 rewrite H1; apply Qeq_refl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H2; simpl; auto.
 rewrite H2; red; simpl; auto.
 generalize H1 (BigN.spec_pos nx); case (BigN.to_Z nx); simpl;
   auto.
 intros HH; case HH; auto.
 intros; red; simpl.
 assert (tmp: forall x, Zneg x = Zopp (Zpos x)); auto.
 rewrite tmp.
 rewrite Zpos_mult_morphism.
 rewrite Z2P_correct; auto.
 ring.
 generalize (BigN.spec_pos dx); auto with zarith.
 intros p _ HH; case HH; auto.
 Qed.

Definition inv_norm (x: t): t := 
 match x with
 | Qz (BigZ.Pos n) => 
   match BigN.compare n BigN.one with
     Gt => Qq BigZ.one n
   | _ =>  x
   end
 | Qz (BigZ.Neg n) => 
   match BigN.compare n BigN.one with
     Gt => Qq BigZ.minus_one n
   | _ =>  x
   end
 | Qq (BigZ.Pos n) d =>
   match BigN.compare n BigN.one with
     Gt => Qq (BigZ.Pos d) n
   | Eq =>  Qz (BigZ.Pos d) 
   | Lt => Qz (BigZ.zero)
   end
 | Qq (BigZ.Neg n) d => 
   match BigN.compare n BigN.one with
     Gt => Qq (BigZ.Neg d) n
   | Eq =>  Qz (BigZ.Neg d) 
   | Lt => Qz (BigZ.zero)
   end
 end.

 Theorem spec_inv_norm : forall x, [inv_norm x] == /[x].
 Proof.
 intros [ [x | x] | [nx | nx] dx]; unfold inv_norm, Qinv.
 match goal with  |- context[BigN.compare ?X ?Y] => 
   generalize (BigN.spec_compare X Y); case BigN.compare
 end; rewrite BigN.spec_1; intros H.
 simpl; rewrite H; apply Qeq_refl.
 case (Zle_lt_or_eq _ _ (BigN.spec_pos x)); simpl.
 generalize H; case BigN.to_Z.
 intros _ HH; discriminate HH.
 intros p; case p; auto.
   intros p1 HH; discriminate HH.
   intros p1 HH; discriminate HH.
 intros HH; discriminate HH.
 intros p _ HH; discriminate HH.
 intros HH; rewrite <- HH.
   apply Qeq_refl.
 generalize H; simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H1.
 rewrite H1; intros HH; discriminate.
 generalize H; case BigN.to_Z.
 intros HH; discriminate HH.
 intros; red; simpl; auto.
 intros p HH; discriminate HH.
 match goal with  |- context[BigN.compare ?X ?Y] => 
   generalize (BigN.spec_compare X Y); case BigN.compare
 end; rewrite BigN.spec_1; intros H.
 simpl; rewrite H; apply Qeq_refl.
 case (Zle_lt_or_eq _ _ (BigN.spec_pos x)); simpl.
 generalize H; case BigN.to_Z.
 intros _ HH; discriminate HH.
 intros p; case p; auto.
   intros p1 HH; discriminate HH.
   intros p1 HH; discriminate HH.
 intros HH; discriminate HH.
 intros p _ HH; discriminate HH.
 intros HH; rewrite <- HH.
   apply Qeq_refl.
 generalize H; simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H1.
 rewrite H1; intros HH; discriminate.
 generalize H; case BigN.to_Z.
 intros HH; discriminate HH.
 intros; red; simpl; auto.
 intros p HH; discriminate HH.
 simpl Qnum.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H1; simpl.
 case BigN.compare; red; simpl; auto.
 rewrite H1; auto.
 case BigN.eq_bool; auto.
 simpl; rewrite H1; auto.
 match goal with  |- context[BigN.compare ?X ?Y] => 
   generalize (BigN.spec_compare X Y); case BigN.compare
 end; rewrite BigN.spec_1; intros H2.
 rewrite H2.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H3.
 case H1; auto.
 red; simpl.
 rewrite Zmult_1_r; rewrite Pmult_1_r; rewrite Z2P_correct; auto.
 generalize (BigN.spec_pos dx); auto with zarith.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H3.
 case H1; auto.
 generalize H2 (BigN.spec_pos nx); case (BigN.to_Z nx).
 intros; apply Qeq_refl.
 intros p; case p; clear p.
 intros p HH; discriminate HH.
 intros p HH; discriminate HH.
 intros HH; discriminate HH.
 intros p _ HH; case HH; auto.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H3.
 case H1; auto.
 simpl; generalize H2; case (BigN.to_Z nx).
 intros HH; discriminate HH.
 intros p Hp.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H4.
 rewrite H4 in H2; discriminate H2.
 red; simpl.
 rewrite Zpos_mult_morphism.
 rewrite Z2P_correct; auto.
 generalize (BigN.spec_pos dx); auto with zarith.
 intros p HH; discriminate HH.
 simpl Qnum.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H1; simpl.
 case BigN.compare; red; simpl; auto.
 rewrite H1; auto.
 case BigN.eq_bool; auto.
 simpl; rewrite H1; auto.
 match goal with  |- context[BigN.compare ?X ?Y] => 
   generalize (BigN.spec_compare X Y); case BigN.compare
 end; rewrite BigN.spec_1; intros H2.
 rewrite H2.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H3.
 case H1; auto.
 red; simpl.
 assert (tmp: forall x, Zneg x = Zopp (Zpos x)); auto.
 rewrite tmp.
 rewrite Zmult_1_r; rewrite Pmult_1_r; rewrite Z2P_correct; auto.
 generalize (BigN.spec_pos dx); auto with zarith.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H3.
 case H1; auto.
 generalize H2 (BigN.spec_pos nx); case (BigN.to_Z nx).
 intros; apply Qeq_refl.
 intros p; case p; clear p.
 intros p HH; discriminate HH.
 intros p HH; discriminate HH.
 intros HH; discriminate HH.
 intros p _ HH; case HH; auto.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H3.
 case H1; auto.
 simpl; generalize H2; case (BigN.to_Z nx).
 intros HH; discriminate HH.
 intros p Hp.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H4.
 rewrite H4 in H2; discriminate H2.
 red; simpl.
 assert (tmp: forall x, Zneg x = Zopp (Zpos x)); auto.
 rewrite tmp.
 rewrite Zpos_mult_morphism.
 rewrite Z2P_correct; auto.
 ring.
 generalize (BigN.spec_pos dx); auto with zarith.
 intros p HH; discriminate HH.
 Qed.

 Definition div x y := mul x (inv y).

 Theorem spec_div x y: [div x y] == [x] / [y].
 Proof.
 intros x y; unfold div; rewrite spec_mul; auto.
 unfold Qdiv; apply Qmult_comp.
 apply Qeq_refl.
 apply spec_inv; auto.
 Qed.

 Definition div_norm x y := mul_norm x (inv y).

 Theorem spec_div_norm x y: [div_norm x y] == [x] / [y].
 Proof.
 intros x y; unfold div_norm; rewrite spec_mul_norm; auto.
 unfold Qdiv; apply Qmult_comp.
 apply Qeq_refl.
 apply spec_inv; auto.
 Qed.

 Definition square (x: t): t :=
  match x with
  | Qz zx => Qz (BigZ.square zx)
  | Qq nx dx => Qq (BigZ.square nx) (BigN.square dx)
  end.

 Theorem spec_square : forall x, [square x] == [x] ^ 2.
 Proof.
 intros [ x | nx dx]; unfold square.
 red; simpl; rewrite BigZ.spec_square; auto with zarith.
 simpl Qpower.
 repeat match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_0; intros H.
 red; simpl.
 repeat match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_0; rewrite BigN.spec_square;
   intros H1.
 case H1; rewrite H; auto.
 red; simpl.
 repeat match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_0; rewrite BigN.spec_square;
   intros H1.
 case H; case (Zmult_integral _ _ H1); auto.
 simpl.
 rewrite BigZ.spec_square.
 rewrite Zpos_mult_morphism.
 assert (tmp: 
  (forall a b, 0 < a -> 0 < b -> Z2P (a * b) = (Z2P a * Z2P b)%positive)%Z).
  intros [|a|a] [|b|b]; simpl; auto; intros; apply False_ind; auto with zarith.
 rewrite tmp; auto.
 generalize (BigN.spec_pos dx); auto with zarith.
 generalize (BigN.spec_pos dx); auto with zarith.
 Qed.

 Definition power_pos (x: t) p: t :=
  match x with
  | Qz zx => Qz (BigZ.power_pos zx p)
  | Qq nx dx => Qq (BigZ.power_pos nx p) (BigN.power_pos dx p)
  end.

 Theorem spec_power_pos : forall x p, [power_pos x p] == [x] ^ Zpos p.
 Proof.
 intros [x | nx dx] p; unfold power_pos.
   unfold power_pos; red; simpl.
   generalize (Qpower_decomp p (BigZ.to_Z x) 1).
   unfold Qeq; simpl.
   rewrite Zpower_pos_1_l; simpl Z2P.
   rewrite Zmult_1_r.
   intros H; rewrite H.
   rewrite BigZ.spec_power_pos; simpl; ring.
 simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_0; rewrite BigN.spec_power_pos; intros H1.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_0; intros H2.
 elim p; simpl.
 intros; red; simpl; auto.
 intros p1 Hp1; rewrite <- Hp1; red; simpl; auto.
 apply Qeq_refl.
 case H2; generalize H1.
 elim p; simpl.
 intros p1 Hrec.
 change (xI p1) with (1 + (xO p1))%positive.
 rewrite Zpower_pos_is_exp; rewrite Zpower_pos_1_r.
 intros HH; case (Zmult_integral _ _ HH); auto.
 rewrite <- Pplus_diag.
 rewrite Zpower_pos_is_exp.
 intros HH1; case (Zmult_integral _ _ HH1); auto.
 intros p1 Hrec.
 rewrite <- Pplus_diag.
 rewrite Zpower_pos_is_exp.
 intros HH1; case (Zmult_integral _ _ HH1); auto.
 rewrite Zpower_pos_1_r; auto.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_0; intros H2.
 case H1; rewrite H2; auto.
 simpl; rewrite Zpower_pos_0_l; auto.
 assert (F1: (0 < BigN.to_Z dx)%Z).
     generalize (BigN.spec_pos dx); auto with zarith.
 assert (F2: (0 < BigN.to_Z dx  ^ ' p)%Z).
  unfold Zpower; apply Zpower_pos_pos; auto.
 unfold power_pos; red; simpl.
 generalize (Qpower_decomp p (BigZ.to_Z nx) 
               (Z2P (BigN.to_Z dx))).
 unfold Qeq; simpl.
 repeat rewrite Z2P_correct; auto.
 unfold Qeq; simpl; intros HH.
 rewrite HH.
 rewrite BigZ.spec_power_pos; simpl; ring.
 Qed.

 (** Interaction with [Qcanon.Qc] *)
 
 Open Scope Qc_scope.

 Definition of_Qc q := of_Q (this q).

 Definition to_Qc q := !!(to_Q q).

 Notation "[[ x ]]" := (to_Qc x).

 Theorem spec_of_Qc: forall q, [[of_Qc q]] = q.
 Proof.
 intros (x, Hx); unfold of_Qc, to_Qc; simpl.
 apply Qc_decomp; simpl.
 intros.
 rewrite <- H0 at 2; apply Qred_complete.
 apply spec_of_Q.
 Qed.

 Theorem spec_oppc: forall q, [[opp q]] = -[[q]].
 Proof.
 intros q; unfold Qcopp, to_Qc, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 rewrite spec_opp.
 rewrite <- Qred_opp.
 rewrite Qred_correct; red; auto.
 Qed.

 Theorem spec_comparec: forall q1 q2,
  compare q1 q2 = ([[q1]] ?= [[q2]]).
 Proof.
 unfold Qccompare, to_Qc. 
 intros q1 q2; rewrite spec_compare; simpl; auto.
 apply Qcompare_comp; apply Qeq_sym; apply Qred_correct.
 Qed.

 Theorem spec_addc x y:
  [[add x y]] = [[x]] + [[y]].
 Proof.
 intros x y; unfold to_Qc.
 apply trans_equal with (!! ([x] + [y])).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_add; auto.
 unfold Qcplus, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 apply Qplus_comp; apply Qeq_sym; apply Qred_correct.
 Qed.

 Theorem spec_add_normc x y:
  [[add_norm x y]] = [[x]] + [[y]].
 Proof.
 intros x y; unfold to_Qc.
 apply trans_equal with (!! ([x] + [y])).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_add_norm; auto.
 unfold Qcplus, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 apply Qplus_comp; apply Qeq_sym; apply Qred_correct.
 Qed.

 Theorem spec_subc x y:  [[sub x y]] = [[x]] - [[y]].
 Proof.
 intros x y; unfold sub; rewrite spec_addc; auto.
 rewrite spec_oppc; ring.
 Qed.

 Theorem spec_sub_normc x y:
   [[sub_norm x y]] = [[x]] - [[y]].
 intros x y; unfold sub_norm; rewrite spec_add_normc; auto.
 rewrite spec_oppc; ring.
 Qed.

 Theorem spec_mulc x y:
  [[mul x y]] = [[x]] * [[y]].
 Proof.
 intros x y; unfold to_Qc.
 apply trans_equal with (!! ([x] * [y])).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_mul; auto.
 unfold Qcmult, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 apply Qmult_comp; apply Qeq_sym; apply Qred_correct.
 Qed.

 Theorem spec_mul_normc x y:
   [[mul_norm x y]] = [[x]] * [[y]].
 Proof.
 intros x y; unfold to_Qc.
 apply trans_equal with (!! ([x] * [y])).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_mul_norm; auto.
 unfold Qcmult, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 apply Qmult_comp; apply Qeq_sym; apply Qred_correct.
 Qed.

 Theorem spec_invc x:
   [[inv x]] =  /[[x]].
 Proof.
 intros x; unfold to_Qc.
 apply trans_equal with (!! (/[x])).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_inv; auto.
 unfold Qcinv, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 apply Qinv_comp; apply Qeq_sym; apply Qred_correct.
 Qed.

 Theorem spec_inv_normc x:
   [[inv_norm x]] =  /[[x]].
 Proof.
 intros x; unfold to_Qc.
 apply trans_equal with (!! (/[x])).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_inv_norm; auto.
 unfold Qcinv, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 apply Qinv_comp; apply Qeq_sym; apply Qred_correct.
 Qed.

 Theorem spec_divc x y: [[div x y]] = [[x]] / [[y]].
 Proof.
 intros x y; unfold div; rewrite spec_mulc; auto.
 unfold Qcdiv; apply f_equal2 with (f := Qcmult); auto.
 apply spec_invc; auto. 
 Qed.

 Theorem spec_div_normc x y: [[div_norm x y]] = [[x]] / [[y]].
 Proof.
 intros x y; unfold div_norm; rewrite spec_mul_normc; auto.
 unfold Qcdiv; apply f_equal2 with (f := Qcmult); auto.
 apply spec_invc; auto.
 Qed.

 Theorem spec_squarec x: [[square x]] =  [[x]]^2.
 Proof.
 intros x; unfold to_Qc.
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

 Theorem spec_power_posc x p:
   [[power_pos x p]] = [[x]] ^ nat_of_P p.
 Proof.
 intros x p; unfold to_Qc.
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
  simpl; case x; simpl; clear x Hrec.
  intros x; simpl; repeat rewrite Qpower_decomp; simpl.
  red; simpl; repeat rewrite Zpower_pos_1_l; simpl Z2P.
  rewrite Pplus_one_succ_l.
  rewrite Zpower_pos_is_exp.
  rewrite Zpower_pos_1_r; auto.
  intros nx dx.
  match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
  end; auto; rewrite BigN.spec_0.
  unfold Qpower_positive.
  assert (tmp: forall p, pow_pos Qmult 0%Q p = 0%Q).
    intros p1; elim p1; simpl; auto; clear p1.
    intros p1 Hp1; rewrite Hp1; auto.
    intros p1 Hp1; rewrite Hp1; auto.
  repeat rewrite tmp; intros; red; simpl; auto.
  intros H1.
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


End Q0.
