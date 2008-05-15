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

Module Qp.

 (** The notation of a rational number is either an integer x,
     interpreted as itself or a pair (x,y) of an integer x and a naturel
     number y interpreted as x/(y+1). *)

 Definition t := q_type.

 Definition zero: t := Qz BigZ.zero.
 Definition one: t := Qz BigZ.one.
 Definition minus_one: t := Qz BigZ.minus_one.

 Definition of_Z x: t := Qz (BigZ.of_Z x).

 Definition d_to_Z d := BigZ.Pos (BigN.succ d).

 Definition of_Q q: t := 
 match q with x # y =>
  Qq (BigZ.of_Z x) (BigN.pred (BigN.of_N (Npos y)))
 end.

 Definition of_Qc q := of_Q (this q).

 Definition to_Q (q: t) := 
 match q with 
  Qz x => BigZ.to_Z x # 1
 |Qq x y => BigZ.to_Z x # Z2P (BigN.to_Z (BigN.succ y))
 end.

 Definition to_Qc q := !!(to_Q q).

 Notation "[[ x ]]" := (to_Qc x).

 Notation "[ x ]" := (to_Q x).

 Theorem spec_to_Q: forall q: Q, [of_Q q] = q.
 intros (x,y); simpl.
 rewrite BigZ.spec_of_Z; auto.
 rewrite BigN.spec_succ; simpl. simpl.
 rewrite BigN.spec_pred; rewrite (BigN.spec_of_pos).
 replace (Zpos y - 1 + 1)%Z with (Zpos y); auto; ring.
 red; auto.
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

 Definition compare (x y: t) :=
  match x, y with
  | Qz zx, Qz zy => BigZ.compare zx zy
  | Qz zx, Qq ny dy => BigZ.compare (BigZ.mul zx (d_to_Z dy)) ny
  | Qq nx dy, Qz zy => BigZ.compare nx (BigZ.mul zy (d_to_Z dy))
  | Qq nx dx, Qq ny dy =>
    BigZ.compare (BigZ.mul nx (d_to_Z dy)) (BigZ.mul ny (d_to_Z dx))
  end.

 Theorem spec_compare: forall q1 q2,
  compare q1 q2 = ([q1] ?= [q2])%Q.
 intros [z1 | x1 y1] [z2 | x2 y2]; unfold Qcompare; simpl.
 repeat rewrite Zmult_1_r.
 generalize (BigZ.spec_compare z1 z2); case BigZ.compare; intros H; auto.
 rewrite H; rewrite Zcompare_refl; auto.
 rewrite Zmult_1_r.
 rewrite BigN.spec_succ.
 rewrite Z2P_correct; auto with zarith.
  2: generalize (BigN.spec_pos y2); auto with zarith.
 generalize (BigZ.spec_compare (z1 * d_to_Z y2) x2)%bigZ; case BigZ.compare; 
   intros H; rewrite <- H.
 rewrite BigZ.spec_mul; unfold d_to_Z; simpl.
 rewrite BigN.spec_succ.
 rewrite Zcompare_refl; auto.
 rewrite BigZ.spec_mul; unfold d_to_Z; simpl.
 rewrite BigN.spec_succ; auto.
 rewrite BigZ.spec_mul; unfold d_to_Z; simpl.
 rewrite BigN.spec_succ; auto.
 rewrite Zmult_1_r.
 rewrite BigN.spec_succ.
 rewrite Z2P_correct; auto with zarith.
  2: generalize (BigN.spec_pos y1); auto with zarith.
 generalize (BigZ.spec_compare x1 (z2 * d_to_Z y1))%bigZ; case BigZ.compare;
    rewrite BigZ.spec_mul; unfold d_to_Z; simpl;  
    rewrite BigN.spec_succ; intros H; auto.
 rewrite H; rewrite Zcompare_refl; auto.
 repeat rewrite BigN.spec_succ; auto.
 repeat rewrite Z2P_correct; auto with zarith.
  2: generalize (BigN.spec_pos y1); auto with zarith.
  2: generalize (BigN.spec_pos y2); auto with zarith.
 generalize (BigZ.spec_compare (x1 * d_to_Z  y2)
                  (x2 * d_to_Z y1))%bigZ; case BigZ.compare;
    repeat rewrite BigZ.spec_mul; unfold d_to_Z; simpl;  
    repeat rewrite BigN.spec_succ; intros H; auto.
 rewrite H; auto.
 rewrite Zcompare_refl; auto.
 Qed.


 Theorem spec_comparec: forall q1 q2,
  compare q1 q2 = ([[q1]] ?= [[q2]]).
 unfold Qccompare, to_Qc. 
 intros q1 q2; rewrite spec_compare; simpl.
 apply Qcompare_comp; apply Qeq_sym; apply Qred_correct.
 Qed.

(* Inv d > 0, Pour la forme normal unique on veut d > 1 *)
 Definition norm n d: t :=
  if BigZ.eq_bool n BigZ.zero then zero
  else
    let gcd := BigN.gcd (BigZ.to_N n) d in
    if BigN.eq_bool gcd BigN.one then Qq n (BigN.pred d)
    else	
      let n := BigZ.div n (BigZ.Pos gcd) in
      let d := BigN.div d gcd in
      if BigN.eq_bool d BigN.one then Qz n
      else Qq n (BigN.pred d).

 Theorem spec_norm: forall n q, 
    ((0 < BigN.to_Z q)%Z -> [norm n q] == [Qq n (BigN.pred q)])%Q.
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
 rewrite BigN.succ_pred; auto with zarith.
 rewrite Z2P_correct; auto with zarith.
 rewrite spec_to_N; intros; rewrite Zgcd_div_swap; auto.
 rewrite H; ring.
 intros H3.
 red; simpl.
 rewrite BigZ.spec_div; simpl; rewrite BigN.spec_gcd; auto with zarith.
 rewrite BigN.succ_pred; auto with zarith.
 assert (F: (0 < BigN.to_Z (q / BigN.gcd (BigZ.to_N p) q)%bigN)%Z).
   rewrite BigN.spec_div; auto with zarith.
   rewrite BigN.spec_gcd.
   apply Zgcd_div_pos; auto.
   rewrite BigN.spec_gcd; auto.
 rewrite BigN.succ_pred; auto with zarith.
 rewrite Z2P_correct; auto.
 rewrite Z2P_correct; auto.
 rewrite BigN.spec_div; simpl; rewrite BigN.spec_gcd; auto with zarith.
 rewrite spec_to_N; apply Zgcd_div_swap; auto.
 case H1; rewrite spec_to_N; rewrite <- Hp; ring.
 Qed.

 Theorem spec_normc: forall n q, 
    (0 < BigN.to_Z q)%Z -> [[norm n q]] = [[Qq n (BigN.pred q)]].
 intros n q H; unfold to_Qc, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_norm; auto.
 Qed.
   
 Definition add (x y: t): t :=
  match x, y with
  | Qz zx, Qz zy => Qz (BigZ.add zx zy)
  | Qz zx, Qq ny dy => Qq (BigZ.add (BigZ.mul zx (d_to_Z dy)) ny) dy
  | Qq nx dx, Qz zy => Qq (BigZ.add nx (BigZ.mul zy (d_to_Z dx))) dx
  | Qq nx dx, Qq ny dy => 
    let dx' := BigN.succ dx in
    let dy' := BigN.succ dy in
    let n := BigZ.add (BigZ.mul nx (BigZ.Pos dy')) (BigZ.mul ny (BigZ.Pos dx')) in
    let d := BigN.pred (BigN.mul dx' dy') in
    Qq n d
  end. 

 Theorem spec_d_to_Z: forall dy,
     (BigZ.to_Z (d_to_Z dy) = BigN.to_Z dy + 1)%Z.
 intros dy; unfold d_to_Z; simpl.
 rewrite BigN.spec_succ; auto.
 Qed.

 Theorem spec_succ_pos: forall p,
  (0 < BigN.to_Z (BigN.succ p))%Z.
 intros p; rewrite BigN.spec_succ;
   generalize (BigN.spec_pos p); auto with zarith.
 Qed.

 Theorem spec_add x y: ([add x y] == [x] + [y])%Q.
 intros [x | nx dx] [y | ny dy]; unfold Qplus; simpl.
 rewrite BigZ.spec_add; repeat rewrite Zmult_1_r; auto.
  apply Qeq_refl; auto.
 assert (F1:= BigN.spec_pos dy).
 rewrite Zmult_1_r.
 simpl; rewrite Z2P_correct; rewrite BigN.spec_succ; auto with zarith.
 rewrite BigZ.spec_add; rewrite BigZ.spec_mul.
 rewrite spec_d_to_Z; apply Qeq_refl.
 assert (F1:= BigN.spec_pos dx).
 rewrite Zmult_1_r; rewrite Pmult_1_r.
 simpl; rewrite Z2P_correct; rewrite BigN.spec_succ; auto with zarith.
 rewrite BigZ.spec_add; rewrite BigZ.spec_mul.
 rewrite spec_d_to_Z; apply Qeq_refl.
 repeat rewrite BigN.spec_succ.
 assert (Fx: (0 < BigN.to_Z dx + 1)%Z).
   generalize (BigN.spec_pos dx); auto with zarith.
 assert (Fy: (0 < BigN.to_Z dy + 1)%Z).
   generalize (BigN.spec_pos dy); auto with zarith.
 repeat rewrite BigN.spec_pred.
 rewrite BigZ.spec_add; repeat rewrite BigN.spec_mul;
   repeat rewrite BigN.spec_succ.
 assert (tmp: forall x, (x-1+1 = x)%Z); [intros; ring | rewrite tmp; clear tmp].
 repeat rewrite Z2P_correct; auto.
 repeat rewrite BigZ.spec_mul; simpl.
 repeat rewrite BigN.spec_succ.
 assert (tmp: 
  (forall a b, 0 < a -> 0 < b -> Z2P (a * b) = (Z2P a * Z2P b)%positive)%Z).
  intros [|a|a] [|b|b]; simpl; auto; intros; apply False_ind; auto with zarith.
 rewrite tmp; auto; apply Qeq_refl.
 rewrite BigN.spec_mul; repeat rewrite BigN.spec_succ; auto with zarith.
 apply Zmult_lt_0_compat; auto.
 Qed.

 Theorem spec_addc x y: [[add x y]] = [[x]] + [[y]].
 intros x y; unfold to_Qc.
 apply trans_equal with (!! ([x] + [y])).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_add.
 unfold Qcplus, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 apply Qplus_comp; apply Qeq_sym; apply Qred_correct.
 Qed.

 Definition add_norm (x y: t): t := 
  match x, y with
  | Qz zx, Qz zy => Qz (BigZ.add zx zy)
  | Qz zx, Qq ny dy => 
    let d := BigN.succ dy in
    norm (BigZ.add (BigZ.mul zx (BigZ.Pos d)) ny) d 
  | Qq nx dx, Qz zy =>
    let d := BigN.succ dx in
    norm (BigZ.add (BigZ.mul zy (BigZ.Pos d)) nx) d
  | Qq nx dx, Qq ny dy =>
    let dx' := BigN.succ dx in
    let dy' := BigN.succ dy in
    let n := BigZ.add (BigZ.mul nx (BigZ.Pos dy')) (BigZ.mul ny (BigZ.Pos dx')) in
    let d := BigN.mul dx' dy' in
    norm n d 
  end.

 Theorem spec_add_norm x y: ([add_norm x y] == [x] + [y])%Q.
 intros x y; rewrite <- spec_add.
 unfold add_norm, add; case x; case y.
  intros; apply Qeq_refl.
 intros p1 n p2.
 match goal with |- [norm ?X ?Y] == _ =>
  apply Qeq_trans with ([Qq X (BigN.pred Y)]);
  [apply spec_norm | idtac]
 end.
 rewrite BigN.spec_succ; generalize (BigN.spec_pos n); auto with zarith.
 simpl.
 repeat rewrite BigZ.spec_add.
 repeat rewrite BigZ.spec_mul; simpl.
 rewrite BigN.succ_pred; try apply Qeq_refl; apply spec_succ_pos.
 intros p1 n p2.
 match goal with |- [norm ?X ?Y] == _ =>
  apply Qeq_trans with ([Qq X (BigN.pred Y)]);
  [apply spec_norm | idtac]
 end.
 rewrite BigN.spec_succ; generalize (BigN.spec_pos p2); auto with zarith.
 simpl.
 repeat rewrite BigZ.spec_add.
 repeat rewrite BigZ.spec_mul; simpl.
 rewrite Zplus_comm.
 rewrite BigN.succ_pred; try apply Qeq_refl; apply spec_succ_pos.
 intros p1 q1 p2 q2.
 match goal with |- [norm ?X ?Y] == _ =>
  apply Qeq_trans with ([Qq X (BigN.pred Y)]);
  [apply spec_norm | idtac]
 end; try apply Qeq_refl.
 rewrite BigN.spec_mul.
 apply Zmult_lt_0_compat; apply spec_succ_pos.
 Qed.

 Theorem spec_add_normc x y: [[add_norm x y]] = [[x]] + [[y]].
 intros x y; unfold to_Qc.
 apply trans_equal with (!! ([x] + [y])).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_add_norm.
 unfold Qcplus, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 apply Qplus_comp; apply Qeq_sym; apply Qred_correct.
 Qed.
 
 Definition sub (x y: t): t := add x (opp y).

 Theorem spec_sub x y: ([sub x y] == [x] - [y])%Q.
 intros x y; unfold sub; rewrite spec_add.
 rewrite spec_opp; ring.
 Qed.

 Theorem spec_subc x y: [[sub x y]] = [[x]] - [[y]].
 intros x y; unfold sub; rewrite spec_addc.
 rewrite spec_oppc; ring.
 Qed.

 Definition sub_norm x y := add_norm x (opp y).

 Theorem spec_sub_norm x y: ([sub_norm x y] == [x] - [y])%Q.
 intros x y; unfold sub_norm; rewrite spec_add_norm.
 rewrite spec_opp; ring.
 Qed.

 Theorem spec_sub_normc x y: [[sub_norm x y]] = [[x]] - [[y]].
 intros x y; unfold sub_norm; rewrite spec_add_normc.
 rewrite spec_oppc; ring.
 Qed.


 Definition mul (x y: t): t :=
  match x, y with
  | Qz zx, Qz zy => Qz (BigZ.mul zx zy)
  | Qz zx, Qq ny dy => Qq (BigZ.mul zx ny) dy
  | Qq nx dx, Qz zy => Qq (BigZ.mul nx zy) dx
  | Qq nx dx, Qq ny dy => 
    Qq (BigZ.mul nx ny) (BigN.pred (BigN.mul (BigN.succ dx) (BigN.succ dy)))
  end.

 Theorem spec_mul x y: ([mul x y] == [x] * [y])%Q.
 intros [x | nx dx] [y | ny dy]; unfold Qmult; simpl.
 rewrite BigZ.spec_mul; repeat rewrite Zmult_1_r; auto.
  apply Qeq_refl; auto.
 rewrite BigZ.spec_mul; apply Qeq_refl.
 rewrite BigZ.spec_mul; rewrite Pmult_1_r; auto.
  apply Qeq_refl; auto.
 assert (F1:= spec_succ_pos dx).
 assert (F2:= spec_succ_pos dy).
 rewrite BigN.succ_pred; rewrite BigN.spec_mul.
 rewrite BigZ.spec_mul.
 assert (tmp: 
  (forall a b, 0 < a -> 0 < b -> Z2P (a * b) = (Z2P a * Z2P b)%positive)%Z).
  intros [|a|a] [|b|b]; simpl; auto; intros; apply False_ind; auto with zarith.
 rewrite tmp; auto; apply Qeq_refl.
 apply Zmult_lt_0_compat; apply spec_succ_pos.
 Qed.

 Theorem spec_mulc x y: [[mul x y]] = [[x]] * [[y]].
 intros x y; unfold to_Qc.
 apply trans_equal with (!! ([x] * [y])).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_mul.
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
      let d := BigN.succ dy in
      let gcd := BigN.gcd (BigZ.to_N zx) d in
      if BigN.eq_bool gcd BigN.one then Qq (BigZ.mul zx ny) dy
      else 
        let zx := BigZ.div zx (BigZ.Pos gcd) in
        let d := BigN.div d gcd in
        if BigN.eq_bool d BigN.one then Qz (BigZ.mul zx ny)
        else Qq (BigZ.mul zx ny) (BigN.pred d)
  | Qq nx dx, Qz zy =>   
    if BigZ.eq_bool zy BigZ.zero then zero
    else	
      let d := BigN.succ dx in
      let gcd := BigN.gcd (BigZ.to_N zy) d in
      if BigN.eq_bool gcd BigN.one then Qq (BigZ.mul zy nx) dx
      else 
        let zy := BigZ.div zy (BigZ.Pos gcd) in
        let d := BigN.div d gcd in
        if BigN.eq_bool d BigN.one then Qz (BigZ.mul zy nx)
        else Qq (BigZ.mul zy nx) (BigN.pred d)
  | Qq nx dx, Qq ny dy => 
    norm (BigZ.mul nx ny) (BigN.mul (BigN.succ dx) (BigN.succ dy))
  end.

 Theorem spec_mul_norm x y: ([mul_norm x y] == [x] * [y])%Q.
 intros x y; rewrite <- spec_mul.
 unfold mul_norm, mul; case x; case y.
  intros; apply Qeq_refl.
 intros p1 n p2.
 match goal with  |- context[BigZ.eq_bool ?X ?Y] => 
   generalize (BigZ.spec_eq_bool X Y); case BigZ.eq_bool
 end; unfold zero, to_Q; repeat rewrite BigZ.spec_0; intros H.
 rewrite BigZ.spec_mul; rewrite H; red; auto.
 assert (F: (0 < BigN.to_Z (BigZ.to_N p2))%Z).
  case (Zle_lt_or_eq _ _ (BigN.spec_pos (BigZ.to_N p2))); auto.
  intros H1; case H; rewrite spec_to_N; rewrite <- H1; ring.
 assert (F1: (0 < BigN.to_Z (BigN.succ n))%Z).
  rewrite BigN.spec_succ; generalize (BigN.spec_pos n); auto with zarith.
 assert (F2: (0 < Zgcd (BigN.to_Z (BigZ.to_N p2)) (BigN.to_Z (BigN.succ n)))%Z).
   case (Zle_lt_or_eq _ _ (Zgcd_is_pos (BigN.to_Z (BigZ.to_N p2))
                                       (BigN.to_Z (BigN.succ n)))); intros H3; auto.
   generalize F; rewrite (Zgcd_inv_0_l _ _ (sym_equal H3)); auto with zarith.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_1; intros H1.
  intros; apply Qeq_refl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_1.
 rewrite BigN.spec_div; rewrite BigN.spec_gcd;
   auto with zarith.
 intros H2.
 red; simpl.
 repeat rewrite BigZ.spec_mul.
 rewrite BigZ.spec_div; simpl; rewrite BigN.spec_gcd; auto with zarith.
 rewrite Z2P_correct; auto with zarith.
 rewrite spec_to_N.
 rewrite Zmult_1_r; repeat rewrite <- Zmult_assoc.
 rewrite (Zmult_comm (BigZ.to_Z p1)).
 repeat rewrite Zmult_assoc.
 rewrite Zgcd_div_swap; auto with zarith.
 rewrite H2; ring.
 intros H2.
 red; simpl.
 repeat rewrite BigZ.spec_mul.
 rewrite BigZ.spec_div; simpl; rewrite BigN.spec_gcd; auto with zarith.
 rewrite Z2P_correct; auto with zarith.
 rewrite (spec_to_N p2).
 case (Zle_lt_or_eq _ _
       (BigN.spec_pos  (BigN.succ n / 
                         BigN.gcd (BigZ.to_N p2) 
                                  (BigN.succ n)))%bigN); intros F3.
 rewrite BigN.succ_pred; auto with zarith.
 rewrite Z2P_correct; auto with zarith.
 rewrite BigN.spec_div; simpl; rewrite BigN.spec_gcd; auto with zarith.
 repeat rewrite <- Zmult_assoc.
 rewrite (Zmult_comm (BigZ.to_Z p1)).
 repeat rewrite Zmult_assoc.
 rewrite Zgcd_div_swap; auto; try ring.
 apply False_ind; generalize F1.
 rewrite (Zdivide_Zdiv_eq
          (Zgcd (BigN.to_Z (BigZ.to_N p2)) (BigN.to_Z (BigN.succ n)))
           (BigN.to_Z (BigN.succ n))); auto.
 generalize F3; rewrite BigN.spec_div; rewrite BigN.spec_gcd;
   auto with zarith.
 intros HH; rewrite <- HH; auto with zarith.
 assert (FF:= Zgcd_is_gcd (BigN.to_Z (BigZ.to_N p2))
           (BigN.to_Z (BigN.succ n))); inversion FF; auto.
 intros p1 p2 n.
 match goal with  |- context[BigZ.eq_bool ?X ?Y] => 
   generalize (BigZ.spec_eq_bool X Y); case BigZ.eq_bool
 end; unfold zero, to_Q; repeat rewrite BigZ.spec_0; intros H.
 rewrite BigZ.spec_mul; rewrite H; red; simpl; ring.
 assert (F: (0 < BigN.to_Z (BigZ.to_N p1))%Z).
  case (Zle_lt_or_eq _ _ (BigN.spec_pos (BigZ.to_N p1))); auto.
  intros H1; case H; rewrite spec_to_N; rewrite <- H1; ring.
 assert (F1: (0 < BigN.to_Z (BigN.succ n))%Z).
  rewrite BigN.spec_succ; generalize (BigN.spec_pos n); auto with zarith.
 assert (F2: (0 < Zgcd (BigN.to_Z (BigZ.to_N p1)) (BigN.to_Z (BigN.succ n)))%Z).
   case (Zle_lt_or_eq _ _ (Zgcd_is_pos (BigN.to_Z (BigZ.to_N p1))
                                       (BigN.to_Z (BigN.succ n)))); intros H3; auto.
   generalize F; rewrite (Zgcd_inv_0_l _ _ (sym_equal H3)); auto with zarith.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_1; intros H1.
  intros; repeat rewrite BigZ.spec_mul; rewrite Zmult_comm; apply Qeq_refl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_1.
 rewrite BigN.spec_div; rewrite BigN.spec_gcd;
   auto with zarith.
 intros H2.
 red; simpl.
 repeat rewrite BigZ.spec_mul.
 rewrite BigZ.spec_div; simpl; rewrite BigN.spec_gcd; auto with zarith.
 rewrite Z2P_correct; auto with zarith.
 rewrite spec_to_N.
 rewrite Zmult_1_r; repeat rewrite <- Zmult_assoc.
 rewrite (Zmult_comm (BigZ.to_Z p2)).
 repeat rewrite Zmult_assoc.
 rewrite Zgcd_div_swap; auto with zarith.
 rewrite H2; ring.
 intros H2.
 red; simpl.
 repeat rewrite BigZ.spec_mul.
 rewrite BigZ.spec_div; simpl; rewrite BigN.spec_gcd; auto with zarith.
 rewrite Z2P_correct; auto with zarith.
 rewrite (spec_to_N p1).
 case (Zle_lt_or_eq _ _
       (BigN.spec_pos  (BigN.succ n / 
                         BigN.gcd (BigZ.to_N p1) 
                                  (BigN.succ n)))%bigN); intros F3.
 rewrite BigN.succ_pred; auto with zarith.
 rewrite Z2P_correct; auto with zarith.
 rewrite BigN.spec_div; simpl; rewrite BigN.spec_gcd; auto with zarith.
 repeat rewrite <- Zmult_assoc.
 rewrite (Zmult_comm (BigZ.to_Z p2)).
 repeat rewrite Zmult_assoc.
 rewrite Zgcd_div_swap; auto; try ring.
 apply False_ind; generalize F1.
 rewrite (Zdivide_Zdiv_eq
          (Zgcd (BigN.to_Z (BigZ.to_N p1)) (BigN.to_Z (BigN.succ n)))
           (BigN.to_Z (BigN.succ n))); auto.
 generalize F3; rewrite BigN.spec_div; rewrite BigN.spec_gcd;
   auto with zarith.
 intros HH; rewrite <- HH; auto with zarith.
 assert (FF:= Zgcd_is_gcd (BigN.to_Z (BigZ.to_N p1))
           (BigN.to_Z (BigN.succ n))); inversion FF; auto.
 intros p1 n1 p2 n2.
 match goal with |- [norm ?X ?Y] == _ =>
  apply Qeq_trans with ([Qq X (BigN.pred Y)]);
  [apply spec_norm | idtac]
 end; try  apply Qeq_refl.
 rewrite BigN.spec_mul.
 apply Zmult_lt_0_compat; rewrite BigN.spec_succ;
    generalize (BigN.spec_pos n1) (BigN.spec_pos n2); auto with zarith.
 Qed.

 Theorem spec_mul_normc x y: [[mul_norm x y]] = [[x]] * [[y]].
 intros x y; unfold to_Qc.
 apply trans_equal with (!! ([x] * [y])).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_mul_norm.
 unfold Qcmult, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 apply Qmult_comp; apply Qeq_sym; apply Qred_correct.
 Qed.

 Definition inv (x: t): t := 
  match x with
  | Qz (BigZ.Pos n) => 
    if BigN.eq_bool n BigN.zero then zero else Qq BigZ.one (BigN.pred n)
  | Qz (BigZ.Neg n) => 
    if BigN.eq_bool n BigN.zero then zero else Qq BigZ.minus_one (BigN.pred n)
  | Qq (BigZ.Pos n) d => 
    if BigN.eq_bool n BigN.zero then zero else Qq (BigZ.Pos (BigN.succ d)) (BigN.pred n)
  | Qq (BigZ.Neg n) d => 
    if BigN.eq_bool n BigN.zero then zero else Qq (BigZ.Neg (BigN.succ d)) (BigN.pred n)
  end.

 Theorem spec_inv x: ([inv x] == /[x])%Q.
 intros [ [x | x] | [nx | nx] dx]; unfold inv.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H.
  unfold zero, to_Q; rewrite BigZ.spec_0.
 unfold BigZ.to_Z; rewrite H; apply Qeq_refl.
 assert (F: (0 < BigN.to_Z x)%Z).
   case (Zle_lt_or_eq _ _ (BigN.spec_pos x)); auto with zarith.
 unfold to_Q; rewrite BigZ.spec_1.
 rewrite BigN.succ_pred; auto.
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
 rewrite BigN.succ_pred; auto.
 generalize F; case BigN.to_Z; simpl; auto with zarith.
 intros p Hp; discriminate Hp.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H.
  unfold zero, to_Q; rewrite BigZ.spec_0.
 unfold BigZ.to_Z; rewrite H; apply Qeq_refl.
 assert (F: (0 < BigN.to_Z nx)%Z).
   case (Zle_lt_or_eq _ _ (BigN.spec_pos nx)); auto with zarith.
 red; unfold Qinv; simpl.
 rewrite BigN.succ_pred; auto.
 rewrite BigN.spec_succ; rewrite Z2P_correct; auto with zarith.
 generalize F; case BigN.to_Z; auto with zarith.
 intros p Hp; discriminate Hp.
 generalize (BigN.spec_pos dx); auto with zarith.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H.
  unfold zero, to_Q; rewrite BigZ.spec_0.
 unfold BigZ.to_Z; rewrite H; apply Qeq_refl.
 assert (F: (0 < BigN.to_Z nx)%Z).
   case (Zle_lt_or_eq _ _ (BigN.spec_pos nx)); auto with zarith.
 red; unfold Qinv; simpl.
 rewrite BigN.succ_pred; auto.
 rewrite BigN.spec_succ; rewrite Z2P_correct; auto with zarith.
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

 Theorem spec_invc x: [[inv x]] =  /[[x]].
 intros x; unfold to_Qc.
 apply trans_equal with (!! (/[x])).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_inv.
 unfold Qcinv, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 apply Qinv_comp; apply Qeq_sym; apply Qred_correct.
 Qed.

Definition inv_norm x := 
 match x with
 | Qz (BigZ.Pos n) => 
      if BigN.eq_bool n BigN.zero then zero else
      if BigN.eq_bool n BigN.one then x else Qq BigZ.one (BigN.pred n)
 | Qz (BigZ.Neg n) => 
      if BigN.eq_bool n BigN.zero then zero  else
      if BigN.eq_bool n BigN.one then x else Qq BigZ.minus_one (BigN.pred n)
 | Qq (BigZ.Pos n) d => let d := BigN.succ d in 
                  if BigN.eq_bool n BigN.zero then zero else
                  if BigN.eq_bool n BigN.one then Qz (BigZ.Pos d) 
                     else Qq (BigZ.Pos d) (BigN.pred n)
 | Qq (BigZ.Neg n) d => let d := BigN.succ d in 
                  if BigN.eq_bool n BigN.zero then zero else
                  if BigN.eq_bool n BigN.one then Qz (BigZ.Neg d) 
                     else Qq (BigZ.Neg d) (BigN.pred n)
 end.

 Theorem spec_inv_norm x: ([inv_norm x] == /[x])%Q.
 intros x; rewrite <- spec_inv.
 (case x; clear x); [intros [x | x] | intros nx dx];
  unfold inv_norm, inv.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H.
  apply Qeq_refl.
 assert (F: (0 < BigN.to_Z x)%Z).
   case (Zle_lt_or_eq _ _ (BigN.spec_pos x)); auto with zarith.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_1; intros H1.
 red; simpl.
 rewrite BigN.succ_pred; auto.
 rewrite Z2P_correct; try rewrite H1; auto with zarith.
  apply Qeq_refl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H.
  apply Qeq_refl.
 assert (F: (0 < BigN.to_Z x)%Z).
   case (Zle_lt_or_eq _ _ (BigN.spec_pos x)); auto with zarith.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_1; intros H1.
 red; simpl.
 rewrite BigN.succ_pred; auto.
 rewrite Z2P_correct; try rewrite H1; auto with zarith.
  apply Qeq_refl.
 case nx; clear nx; intros nx.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H.
  apply Qeq_refl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_1; intros H1.
 red; simpl.
 rewrite BigN.succ_pred; try rewrite H1; auto with zarith.
 apply Qeq_refl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H.
  apply Qeq_refl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_1; intros H1.
 red; simpl.
 rewrite BigN.succ_pred; try rewrite H1; auto with zarith.
 apply Qeq_refl.
 Qed.


 Definition div x y := mul x (inv y).

 Theorem spec_div x y: ([div x y] == [x] / [y])%Q.
 intros x y; unfold div; rewrite spec_mul; auto.
 unfold Qdiv; apply Qmult_comp.
 apply Qeq_refl.
 apply spec_inv; auto.
 Qed.

 Theorem spec_divc x y: [[div x y]] = [[x]] / [[y]].
 intros x y; unfold div; rewrite spec_mulc; auto.
 unfold Qcdiv; apply f_equal2 with (f := Qcmult); auto.
 apply spec_invc; auto. 
 Qed.

 Definition div_norm x y := mul_norm x (inv y).

 Theorem spec_div_norm x y: ([div_norm x y] == [x] / [y])%Q.
 intros x y; unfold div_norm; rewrite spec_mul_norm; auto.
 unfold Qdiv; apply Qmult_comp.
 apply Qeq_refl.
 apply spec_inv; auto.
 Qed.

 Theorem spec_div_normc x y: [[div_norm x y]] = [[x]] / [[y]].
 intros x y; unfold div_norm; rewrite spec_mul_normc; auto.
 unfold Qcdiv; apply f_equal2 with (f := Qcmult); auto.
 apply spec_invc; auto.
 Qed.


 Definition square (x: t): t :=
  match x with
  | Qz zx => Qz (BigZ.square zx)
  | Qq nx dx => Qq (BigZ.square nx) (BigN.pred (BigN.square (BigN.succ dx)))
  end.

 Theorem spec_square x: ([square x] == [x] ^ 2)%Q.
 intros [ x | nx dx]; unfold square.
 red; simpl; rewrite BigZ.spec_square; auto with zarith.
 red; simpl; rewrite BigZ.spec_square; auto with zarith.
 assert (F: (0 < BigN.to_Z (BigN.succ dx))%Z).
   rewrite BigN.spec_succ;
   case (Zle_lt_or_eq _ _ (BigN.spec_pos dx)); auto with zarith.
 assert (F1 : (0 < BigN.to_Z (BigN.square (BigN.succ dx)))%Z).
   rewrite BigN.spec_square; apply Zmult_lt_0_compat;
     auto with zarith.
 rewrite BigN.succ_pred; auto.
 rewrite Zpos_mult_morphism.
 repeat rewrite Z2P_correct; auto with zarith.
 repeat rewrite BigN.spec_succ; auto with zarith.
 rewrite BigN.spec_square; auto with zarith.
 repeat rewrite BigN.spec_succ; auto with zarith.
 Qed.

 Theorem spec_squarec x: [[square x]] =  [[x]]^2.
 intros x; unfold to_Qc.
 apply trans_equal with (!! ([x]^2)).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_square.
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
  | Qq nx dx => Qq (BigZ.power_pos nx p) (BigN.pred (BigN.power_pos (BigN.succ dx) p))
  end.


 Theorem spec_power_pos x p: ([power_pos x p] == [x] ^ Zpos p)%Q.
 Proof.
 intros [x | nx dx] p; unfold power_pos.
   unfold power_pos; red; simpl.
   generalize (Qpower_decomp p (BigZ.to_Z x) 1).
   unfold Qeq; simpl.
   rewrite Zpower_pos_1_l; simpl Z2P.
   rewrite Zmult_1_r.
   intros H; rewrite H.
   rewrite BigZ.spec_power_pos; simpl; ring.
 assert (F1: (0 < BigN.to_Z (BigN.succ dx))%Z).
     rewrite BigN.spec_succ;
     generalize (BigN.spec_pos dx); auto with zarith.
 assert (F2: (0 < BigN.to_Z (BigN.succ dx) ^ ' p)%Z).
  unfold Zpower; apply Zpower_pos_pos; auto.
 unfold power_pos; red; simpl.
 rewrite BigN.succ_pred; rewrite BigN.spec_power_pos; auto.
 rewrite Z2P_correct; auto.
 generalize (Qpower_decomp p (BigZ.to_Z nx) 
               (Z2P (BigN.to_Z (BigN.succ dx)))).
 unfold Qeq; simpl.
 repeat rewrite Z2P_correct; auto.
 unfold Qeq; simpl; intros HH.
 rewrite HH.
 rewrite BigZ.spec_power_pos; simpl; ring.
 Qed.

 Theorem spec_power_posc x p: [[power_pos x p]] = [[x]] ^ nat_of_P p.
 intros x p; unfold to_Qc.
 apply trans_equal with (!! ([x]^Zpos p)).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_power_pos.
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
  intros nx dx; simpl; repeat rewrite Qpower_decomp; simpl.
  red; simpl; repeat rewrite Zpower_pos_1_l; simpl Z2P.
  rewrite Pplus_one_succ_l.
  rewrite Zpower_pos_is_exp.
  rewrite Zpower_pos_1_r; auto.
  assert (F1: (0 < BigN.to_Z (BigN.succ dx))%Z).
    rewrite BigN.spec_succ; generalize (BigN.spec_pos dx); 
      auto with zarith.
  repeat rewrite Zpos_mult_morphism.
  repeat rewrite Z2P_correct; auto.
  2: apply Zpower_pos_pos; auto.
  2: apply Zpower_pos_pos; auto.
  rewrite Zpower_pos_is_exp.
  rewrite Zpower_pos_1_r; auto.
 rewrite F.
 apply Qmult_comp; apply Qeq_sym; apply Qred_correct.
 Qed.


End Qp.
