Require Import Bool.
Require Import ZArith.
Require Import Znumtheory.
Require Import ZAux.
Require Import Arith.
Require Export BigN.
Require Export BigZ.
Require Import QArith.
Require Import Qcanon.
Require Import Qpower.
Require Import QMake_base.	

Module Qbi.

 (* Troisieme solution :
    0 a de nombreuse representation :
         0, -0, 1/0, ... n/0,
    il faut alors faire attention avec la comparaison et l'addition 
    
    Les fonctions de normalization s'effectue seulement si les
    nombres sont grands.
 *)

 Definition t := q_type.

 Definition zero:t := Qz BigZ.zero.
 Definition one: t  := Qz BigZ.one.
 Definition minus_one: t := Qz BigZ.minus_one.

 Definition of_Z x: t := Qz (BigZ.of_Z x).


 Definition of_Q q: t := 
 match q with x # y =>
  Qq (BigZ.of_Z x) (BigN.of_N (Npos y))
 end.

 Definition of_Qc q := of_Q (this q).

 Definition to_Q (q: t) := 
 match q with 
  Qz x => BigZ.to_Z x # 1
 |Qq x y => if BigN.eq_bool y BigN.zero then 0%Q
            else BigZ.to_Z x # Z2P (BigN.to_Z y)
 end.

 Definition to_Qc q := !!(to_Q q).

 Notation "[[ x ]]" := (to_Qc x).

 Notation "[ x ]" := (to_Q x).

 Theorem spec_to_Q: forall q: Q, [of_Q q] = q.
 intros (x,y); simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
  generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_0.
   rewrite BigN.spec_of_pos; intros HH; discriminate HH.
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

 Theorem spec_opp: forall q, ([opp q] = -[q])%Q.
 intros [z | x y]; simpl.
 rewrite BigZ.spec_opp; auto.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
  generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_0.
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
  | Qz zx, Qq ny dy => 
    if BigN.eq_bool dy BigN.zero then BigZ.compare zx BigZ.zero
    else
      match BigZ.cmp_sign zx ny with
      | Lt => Lt 
      | Gt => Gt
      | Eq => BigZ.compare (BigZ.mul zx (BigZ.Pos dy)) ny
      end
  | Qq nx dx, Qz zy =>
    if BigN.eq_bool dx BigN.zero then BigZ.compare BigZ.zero zy     
    else
      match BigZ.cmp_sign nx zy with
      | Lt => Lt
      | Gt => Gt
      | Eq => BigZ.compare nx (BigZ.mul zy (BigZ.Pos dx))
      end
  | Qq nx dx, Qq ny dy =>
    match BigN.eq_bool dx BigN.zero, BigN.eq_bool dy BigN.zero with
    | true, true => Eq
    | true, false => BigZ.compare BigZ.zero ny
    | false, true => BigZ.compare nx BigZ.zero
    | false, false =>
      match BigZ.cmp_sign nx ny with
      | Lt => Lt
      | Gt => Gt
      | Eq => BigZ.compare (BigZ.mul nx (BigZ.Pos dy)) (BigZ.mul ny (BigZ.Pos dx))
      end
    end
  end.

 Theorem spec_compare: forall q1 q2, 
  compare q1 q2 = ([q1] ?= [q2])%Q.
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
 set (a := BigZ.to_Z z1); set (b := BigZ.to_Z x2);
   set (c := BigN.to_Z y2); fold c in HH.
 assert (F: (0 < c)%Z).
   case (Zle_lt_or_eq _ _ (BigN.spec_pos  y2)); fold c; auto.
   intros H1; case HH; rewrite <- H1; auto.
 rewrite Z2P_correct; auto with zarith.
 generalize (BigZ.spec_cmp_sign z1 x2); case BigZ.cmp_sign; fold a b c.
 intros _; generalize (BigZ.spec_compare (z1 * BigZ.Pos y2)%bigZ x2); 
   case BigZ.compare; rewrite BigZ.spec_mul; simpl; fold a b c; auto.
 intros H1; rewrite H1; rewrite Zcompare_refl; auto.
 intros (H1, H2); apply sym_equal; change (a * c < b)%Z.
 apply Zlt_le_trans with (2 := H2).
 change 0%Z with (0 * c)%Z.
 apply Zmult_lt_compat_r; auto with zarith.
 intros (H1, H2); apply sym_equal; change (a * c > b)%Z.
 apply Zlt_gt.
 apply Zlt_le_trans with (1 := H2).
 change 0%Z with (0 * c)%Z.
 apply Zmult_le_compat_r; auto with zarith.
 generalize (BigN.spec_eq_bool y1 BigN.zero);
   case BigN.eq_bool; rewrite BigN.spec_0; intros HH.
 rewrite Zmult_0_l; rewrite Zmult_1_r.
 generalize (BigZ.spec_compare BigZ.zero z2);
  case BigZ.compare; auto.
 rewrite BigZ.spec_0; intros HH1; rewrite <- HH1; rewrite Zcompare_refl; auto.
 set (a := BigZ.to_Z z2); set (b := BigZ.to_Z x1);
   set (c := BigN.to_Z y1); fold c in HH.
 assert (F: (0 < c)%Z).
   case (Zle_lt_or_eq _ _ (BigN.spec_pos  y1)); fold c; auto.
   intros H1; case HH; rewrite <- H1; auto.
 rewrite Zmult_1_r; rewrite Z2P_correct; auto with zarith.
 generalize (BigZ.spec_cmp_sign x1 z2); case BigZ.cmp_sign; fold a b c.
 intros _; generalize (BigZ.spec_compare x1 (z2 * BigZ.Pos y1)%bigZ); 
   case BigZ.compare; rewrite BigZ.spec_mul; simpl; fold a b c; auto.
 intros H1; rewrite H1; rewrite Zcompare_refl; auto.
 intros (H1, H2); apply sym_equal; change (b < a * c)%Z.
 apply Zlt_le_trans with (1 := H1).
 change 0%Z with (0 * c)%Z.
 apply Zmult_le_compat_r; auto with zarith.
 intros (H1, H2); apply sym_equal; change (b > a * c)%Z.
 apply Zlt_gt.
 apply Zlt_le_trans with (2 := H1).
 change 0%Z with (0 * c)%Z.
 apply Zmult_lt_compat_r; auto with zarith.
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
 set (a := BigZ.to_Z x1); set (b := BigZ.to_Z x2);
   set (c1 := BigN.to_Z y1); set (c2 := BigN.to_Z y2).
 fold c1 in HH; fold c2 in HH1.
 assert (F1: (0 < c1)%Z).
   case (Zle_lt_or_eq _ _ (BigN.spec_pos  y1)); fold c1; auto.
   intros H1; case HH; rewrite <- H1; auto.
 assert (F2: (0 < c2)%Z).
   case (Zle_lt_or_eq _ _ (BigN.spec_pos  y2)); fold c2; auto.
   intros H1; case HH1; rewrite <- H1; auto.
 repeat rewrite Z2P_correct; auto.
 generalize (BigZ.spec_cmp_sign x1 x2); case BigZ.cmp_sign.
 intros _; generalize (BigZ.spec_compare (x1 * BigZ.Pos y2)%bigZ
                          (x2 * BigZ.Pos y1)%bigZ); 
   case BigZ.compare; rewrite BigZ.spec_mul; simpl; fold a b c1 c2; auto.
 rewrite BigZ.spec_mul; simpl; fold a b c1; intros HH2; rewrite HH2;
  rewrite Zcompare_refl; auto.
 rewrite BigZ.spec_mul; simpl; auto.
 rewrite BigZ.spec_mul; simpl; auto.
 fold a b; intros (H1, H2); apply sym_equal; change (a * c2 < b * c1)%Z.
 apply Zlt_le_trans with 0%Z.
   change 0%Z with (0 * c2)%Z.
 apply Zmult_lt_compat_r; auto with zarith.
 apply Zmult_le_0_compat; auto with zarith.
 fold a b; intros (H1, H2); apply sym_equal; change (a * c2 > b * c1)%Z.
 apply Zlt_gt; apply Zlt_le_trans with 0%Z.
 change 0%Z with (0 * c1)%Z.
 apply Zmult_lt_compat_r; auto with zarith.
 apply Zmult_le_0_compat; auto with zarith.
 Qed.


 Definition do_norm_n n := 
  match n with
  | BigN.N0 _ => false
  | BigN.N1 _ => false
  | BigN.N2 _ => false
  | BigN.N3 _ => false
  | BigN.N4 _ => false
  | BigN.N5 _ => false
  | BigN.N6 _ => false
  | BigN.N7 _ => false
  | BigN.N8 _ => false
  | _         => true 
  end.
 
 Definition do_norm_z z :=
  match z with
  | BigZ.Pos n => do_norm_n n
  | BigZ.Neg n => do_norm_n n
  end.

(* Je pense que cette fonction normalise bien ... *)
 Definition norm n d: t :=
  if andb (do_norm_z n) (do_norm_n d) then
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
  end
 else Qq n d.

 Theorem spec_norm: forall n q, 
     ([norm n q] == [Qq n q])%Q.
 intros p q; unfold norm.
 case do_norm_z; simpl andb.
 2: apply Qeq_refl.
 case do_norm_n.
 2: apply Qeq_refl.
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
       if BigN.eq_bool dx dy then
         let n := BigZ.add nx ny in
         Qq n dx
       else
         let n := BigZ.add (BigZ.mul nx (BigZ.Pos dy)) (BigZ.mul ny (BigZ.Pos dx)) in
         let d := BigN.mul dx dy in
         Qq n d
    end
  end.



 Theorem spec_add x y: 
  ([add x y] == [x] + [y])%Q.
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
 generalize (BigN.spec_eq_bool dx dy);
   case BigN.eq_bool; intros HH3.
 rewrite <- HH3.
 assert (Fx: (0 < BigN.to_Z dx)%Z).
   generalize (BigN.spec_pos dx); auto with zarith.
 red; simpl.
 generalize (BigN.spec_eq_bool dx BigN.zero);
   case BigN.eq_bool; rewrite BigN.spec_0; intros HH4.
 case HH; auto.
 simpl; rewrite Zpos_mult_morphism.
 repeat rewrite Z2P_correct; auto with zarith.
 rewrite BigZ.spec_add; repeat rewrite BigZ.spec_mul; simpl.
 ring.
 assert (Fx: (0 < BigN.to_Z dx)%Z).
   generalize (BigN.spec_pos dx); auto with zarith.
 assert (Fy: (0 < BigN.to_Z dy)%Z).
   generalize (BigN.spec_pos dy); auto with zarith.
 red; simpl; rewrite Zpos_mult_morphism.
 repeat rewrite Z2P_correct; auto with zarith.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; auto; rewrite BigN.spec_mul;
    rewrite BigN.spec_0; intros H3; simpl.
 absurd (0 < 0)%Z; auto with zarith.
 rewrite BigZ.spec_add; repeat rewrite BigZ.spec_mul; simpl.
 repeat rewrite Z2P_correct; auto with zarith.
 apply Zmult_lt_0_compat; auto.
 Qed.

 Theorem spec_addc x y:
  [[add x y]] = [[x]] + [[y]].
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

 Definition add_norm (x y: t): t :=
  match x with
  | Qz zx =>
    match y with
    | Qz zy => Qz (BigZ.add zx zy)
    | Qq ny dy =>  
      if BigN.eq_bool dy BigN.zero then x 
      else 
        norm (BigZ.add (BigZ.mul zx (BigZ.Pos dy)) ny) dy
    end
  | Qq nx dx =>
    if BigN.eq_bool dx BigN.zero then y 
    else match y with
    | Qz zy => norm (BigZ.add nx (BigZ.mul zy (BigZ.Pos dx))) dx
    | Qq ny dy =>
      if BigN.eq_bool dy BigN.zero then x
      else
       if BigN.eq_bool dx dy then
         let n := BigZ.add nx ny in
         norm n dx
       else
         let n := BigZ.add (BigZ.mul nx (BigZ.Pos dy)) (BigZ.mul ny (BigZ.Pos dx)) in
         let d := BigN.mul dx dy in
         norm n d
    end
  end.

 Theorem spec_add_norm x y:
  ([add_norm x y] == [x] + [y])%Q.
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
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; intros HH3;
 match goal with |- [norm ?X ?Y] == _ =>
  apply Qeq_trans with ([Qq X Y]);
  [apply spec_norm | idtac]
 end; apply Qeq_refl.
 Qed.

 Theorem spec_add_normc x y:
  [[add_norm x y]] = [[x]] + [[y]].
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
 
 Definition sub x y := add x (opp y).

 Theorem spec_sub x y:
  ([sub x y] == [x] - [y])%Q.
 intros x y; unfold sub; rewrite spec_add; auto.
 rewrite spec_opp; ring.
 Qed.

 Theorem spec_subc x y:  [[sub x y]] = [[x]] - [[y]].
 intros x y; unfold sub; rewrite spec_addc; auto.
 rewrite spec_oppc; ring.
 Qed.

 Definition sub_norm x y := add_norm x (opp y).

 Theorem spec_sub_norm x y: 
  ([sub_norm x y] == [x] - [y])%Q.
 intros x y; unfold sub_norm; rewrite spec_add_norm; auto.
 rewrite spec_opp; ring.
 Qed.

 Theorem spec_sub_normc x y:
   [[sub_norm x y]] = [[x]] - [[y]].
 intros x y; unfold sub_norm; rewrite spec_add_normc; auto.
 rewrite spec_oppc; ring.
 Qed.

 Definition mul (x y: t): t :=
  match x, y with
  | Qz zx, Qz zy => Qz (BigZ.mul zx zy)
  | Qz zx, Qq ny dy => Qq (BigZ.mul zx ny) dy
  | Qq nx dx, Qz zy => Qq (BigZ.mul nx zy) dx
  | Qq nx dx, Qq ny dy => Qq (BigZ.mul nx ny) (BigN.mul dx dy)
  end.

 Theorem spec_mul x y: ([mul x y] == [x] * [y])%Q.
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

 Theorem spec_mulc x y:
  [[mul x y]] = [[x]] * [[y]].
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

 Definition mul_norm (x y: t): t := 
  match x, y with
  | Qz zx, Qz zy => Qz (BigZ.mul zx zy)
  | Qz zx, Qq ny dy => mul (Qz ny) (norm zx dy)
  | Qq nx dx, Qz zy => mul (Qz nx) (norm zy dx)
  | Qq nx dx, Qq ny dy => mul (norm nx dy) (norm ny dx)
  end.

 Theorem spec_mul_norm x y:
  ([mul_norm x y] == [x] * [y])%Q.
 intros x y; rewrite <- spec_mul; auto.
 unfold mul_norm; case x; case y; clear x y.
  intros; apply Qeq_refl.
 intros p1 n p2.
 repeat rewrite spec_mul.
 match goal with |- ?Z == _ =>
   match Z with context id [norm ?X ?Y] =>
   let y := context id [Qq X Y] in
   apply Qeq_trans with y; [repeat apply Qmult_comp;
   repeat apply Qplus_comp; repeat apply Qeq_refl;
   apply spec_norm | idtac]
   end
 end.
 red; simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros HH; simpl; ring.
 intros p1 p2 n.
 repeat rewrite spec_mul.
 match goal with |- ?Z == _ =>
   match Z with context id [norm ?X ?Y] =>
   let y := context id [Qq X Y] in
   apply Qeq_trans with y; [repeat apply Qmult_comp;
   repeat apply Qplus_comp; repeat apply Qeq_refl;
   apply spec_norm | idtac]
   end
 end.
 red; simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros HH; simpl; try ring.
 rewrite Pmult_1_r; auto.
 intros p1 n1 p2 n2.
 repeat rewrite spec_mul.
 repeat match goal with |- ?Z == _ =>
   match Z with context id [norm ?X ?Y] =>
   let y := context id [Qq X Y] in
   apply Qeq_trans with y; [repeat apply Qmult_comp;
   repeat apply Qplus_comp; repeat apply Qeq_refl;
   apply spec_norm | idtac]
   end
 end.
 red; simpl.
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H1;
 match goal with  |- context[BigN.eq_bool ?X ?Y] => 
   generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
 end; rewrite BigN.spec_0; intros H2; simpl; try ring.
 repeat rewrite Zpos_mult_morphism; ring.
 Qed.

 Theorem spec_mul_normc x y:
   [[mul_norm x y]] = [[x]] * [[y]].
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

 Definition inv (x: t): t := 
  match x with
  | Qz (BigZ.Pos n) => Qq BigZ.one n
  | Qz (BigZ.Neg n) => Qq BigZ.minus_one n
  | Qq (BigZ.Pos n) d => Qq (BigZ.Pos d) n
  | Qq (BigZ.Neg n) d => Qq (BigZ.Neg d) n
  end.


 Theorem spec_inv x:
   ([inv x] == /[x])%Q.
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

 Theorem spec_invc x:
   [[inv x]] =  /[[x]].
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

 Definition inv_norm (x: t): t := 
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

 Theorem spec_inv_norm x: ([inv_norm x] == /[x])%Q.
 intros x; rewrite <- spec_inv; generalize x; clear x.
 intros [ [x | x] | [nx | nx] dx]; unfold inv_norm, inv;
   match goal with  |- context[BigN.eq_bool ?X ?Y] => 
     generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
   end; rewrite BigN.spec_0; intros H1; try apply Qeq_refl;
   red; simpl;
   match goal with  |- context[BigN.eq_bool ?X ?Y] => 
     generalize (BigN.spec_eq_bool X Y); case BigN.eq_bool
   end; rewrite BigN.spec_0; intros H2; auto;
   case H2; auto.
 Qed.

 Theorem spec_inv_normc x:
   [[inv_norm x]] =  /[[x]].
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
  | Qq nx dx => Qq (BigZ.square nx) (BigN.square dx)
  end.


 Theorem spec_square x: ([square x] == [x] ^ 2)%Q.
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

 Theorem spec_squarec x: [[square x]] =  [[x]]^2.
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

 Definition power_pos (x: t) p: t :=
  match x with
  | Qz zx => Qz (BigZ.power_pos zx p)
  | Qq nx dx => Qq (BigZ.power_pos nx p) (BigN.power_pos dx p)
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

 Theorem spec_power_posc x p:
   [[power_pos x p]] = [[x]] ^ nat_of_P p.
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


End Qbi.




