Require Import ZArith.
Require Import ZAux.
Require Import ZDivModAux.
Require Import Basic_type.

(* To compute the necessary height *)

Fixpoint plength (p: positive) : positive :=
  match p with 
    xH => xH
  | xO p1 => Psucc (plength p1)
  | xI p1 => Psucc (plength p1)
  end.

Theorem plength_correct: forall p, (Zpos p < 2 ^ Zpos (plength p))%Z.
assert (F: (forall p, 2 ^ (Zpos (Psucc p)) = 2 * 2 ^ Zpos p)%Z).
intros p; replace (Zpos (Psucc p)) with (1 + Zpos p)%Z.
rewrite Zpower_exp; auto with zarith.
rewrite Zpos_succ_morphism; unfold Zsucc; auto with zarith.
intros p; elim p; simpl plength; auto.
intros p1 Hp1; rewrite F; repeat rewrite Zpos_xI.
assert (tmp: (forall p, 2 * p = p + p)%Z); 
  try repeat rewrite tmp; auto with zarith.
intros p1 Hp1; rewrite F; rewrite (Zpos_xO p1).
assert (tmp: (forall p, 2 * p = p + p)%Z); 
  try repeat rewrite tmp; auto with zarith.
rewrite ZPowerAux.Zpower_exp_1; auto with zarith.
Qed.

Theorem plength_pred_correct: forall p, (Zpos p <= 2 ^ Zpos (plength (Ppred p)))%Z.
intros p; case (Psucc_pred p); intros H1.
subst; simpl plength.
rewrite ZPowerAux.Zpower_exp_1; auto with zarith.
pattern p at 1; rewrite <- H1.
rewrite Zpos_succ_morphism; unfold Zsucc; auto with zarith.
generalize (plength_correct (Ppred p)); auto with zarith.
Qed.

Definition Pdiv p q :=
  match Zdiv (Zpos p) (Zpos q) with
    Zpos q1 => match (Zpos p) - (Zpos q) * (Zpos q1) with
                 Z0 => q1
               | _ => (Psucc q1)
               end
  |  _ => xH
  end.

Theorem Pdiv_le: forall p q,
  Zpos p <= Zpos q * Zpos (Pdiv p q).
intros p q.
unfold Pdiv.
assert (H1: Zpos q > 0); auto with zarith.
assert (H1b: Zpos p >= 0); auto with zarith.
generalize (Z_div_ge0 (Zpos p) (Zpos q) H1 H1b).
generalize (Z_div_mod_eq (Zpos p) (Zpos q) H1); case Zdiv.
  intros HH _; rewrite HH; rewrite Zmult_0_r; rewrite Zmult_1_r; simpl.
case (Z_mod_lt (Zpos p) (Zpos q) H1); auto with zarith.
intros q1 H2.
replace (Zpos p - Zpos q * Zpos q1) with (Zpos p mod Zpos q).
  2: pattern (Zpos p) at 2; rewrite H2; auto with zarith.
generalize H2 (Z_mod_lt (Zpos p) (Zpos q) H1); clear H2; 
  case Zmod.
  intros HH _; rewrite HH; auto with zarith.
  intros r1 HH (_,HH1); rewrite HH; rewrite Zpos_succ_morphism.
  unfold Zsucc; rewrite Zmult_plus_distr_r; auto with zarith.
  intros r1 _ (HH,_); case HH; auto.
intros q1 HH; rewrite HH.
unfold Zge; simpl Zcompare; intros HH1; case HH1; auto.
Qed.

Definition is_one p := match p with xH => true | _ => false end.

Theorem is_one_one: forall p, is_one p = true -> p = xH.
intros p; case p; auto; intros p1 H1; discriminate H1.
Qed.

Definition get_height digits p :=
  let r := Pdiv p digits in
   if is_one r then xH else Psucc (plength (Ppred r)).

Theorem get_height_correct:
  forall digits N,
   Zpos N <= Zpos digits * (2 ^ (Zpos (get_height digits N) -1)).
intros digits N.
unfold get_height.
assert (H1 := Pdiv_le N digits).
case_eq (is_one (Pdiv N digits)); intros H2.
rewrite (is_one_one _ H2) in H1.
rewrite Zmult_1_r in H1.
change (2^(1-1))%Z with 1; rewrite Zmult_1_r; auto.
clear H2.
apply Zle_trans with (1 := H1).
apply Zmult_le_compat_l; auto with zarith.
rewrite Zpos_succ_morphism; unfold Zsucc.
rewrite Zplus_comm; rewrite Zminus_plus.
apply plength_pred_correct.
Qed.



Definition zn2z_word_comm : forall w n, zn2z (word w n) = word (zn2z w) n.
 fix zn2z_word_comm 2.
 intros w n; case n.
  reflexivity.
  intros n0;simpl.
  case (zn2z_word_comm w n0).
  reflexivity.
Defined.

Fixpoint extend (n:nat) {struct n} : forall w:Set, zn2z w -> word w (S n) :=
 match n return forall w:Set, zn2z w -> word w (S n) with 
 | O => fun w x => x
 | S m => 
   let aux := extend m in
   fun w x => WW W0 (aux w x)
 end.

Section ExtendMax.

 Variable w:Set.

 Definition Tmax n m :=
  (  {p:nat| word (word w n) p = word w m} 
    + {p:nat| word (word w m) p = word w n})%type.

 Definition max : forall n m, Tmax n m.
  fix max 1;intros n.
  case n.
  intros m;left;exists m;exact (refl_equal (word w m)).
  intros n0 m;case m.
  right;exists (S n0);exact (refl_equal (word w (S n0))).
  intros m0;case (max n0 m0);intros H;case H;intros p Heq.
  left;exists p;simpl.
   case (zn2z_word_comm (word w n0) p).
   case Heq.
   exact (refl_equal (zn2z (word (word w n0) p))).
  right;exists p;simpl.
   case (zn2z_word_comm (word w m0) p).
   case Heq.
   exact (refl_equal (zn2z (word (word w m0) p))).
 Defined.

 Definition extend_to_max : 
  forall n m (x:zn2z (word w n)) (y:zn2z (word w m)), 
        (zn2z (word w m) + zn2z (word w n))%type.
  intros n m x y.
   case (max n m);intros (p, Heq);case Heq.
   left;exact (extend p (word w n) x).
   right;exact (extend p (word w m) y).
 Defined. 

End ExtendMax.

Section Reduce.

 Variable w : Set.
 Variable nT : Set.
 Variable N0 : nT.
 Variable eq0 : w -> bool.
 Variable reduce_n : w -> nT.
 Variable zn2z_to_Nt : zn2z w -> nT.

 Definition reduce_n1 (x:zn2z w) :=
  match x with
  | W0 => N0
  | WW xh xl =>
    if eq0 xh then reduce_n xl
    else zn2z_to_Nt x
  end.

End Reduce.

Section ReduceRec.

 Variable w : Set.
 Variable nT : Set.
 Variable N0 : nT.
 Variable reduce_1n : zn2z w -> nT.
 Variable c : forall n, word w (S n) -> nT.

 Fixpoint reduce_n (n:nat) : word w (S n) -> nT :=
  match n return word w (S n) -> nT with
  | O => reduce_1n
  | S m => fun x =>
    match x with
    | W0 => N0
    | WW xh xl =>
      match xh with
      | W0 => @reduce_n m xl
      | _ => @c (S m) x 
      end
    end	
  end.

End ReduceRec.

Definition opp_compare cmp :=
  match cmp with
  | Lt => Gt
  | Eq => Eq
  | Gt => Lt
  end.

Section CompareRec.

 Variable wm w : Set.
 Variable w_0 : w.
 Variable compare : w -> w -> comparison.
 Variable compare0_m : wm -> comparison.
 Variable compare_m : wm -> w -> comparison.

 Fixpoint compare0_mn (n:nat) : word wm n -> comparison :=
  match n return word wm n -> comparison with 
  | O => compare0_m 
  | S m => fun x =>
    match x with
    | W0 => Eq
    | WW xh xl => 
      match compare0_mn m xh with
      | Eq => compare0_mn m xl 
      | r  => Lt
      end
    end
  end.

 Fixpoint compare_mn_1 (n:nat) : word wm n -> w -> comparison :=
  match n return word wm n -> w -> comparison with 
  | O => compare_m 
  | S m => fun x y => 
    match x with
    | W0 => compare w_0 y
    | WW xh xl => 
      match compare0_mn m xh with
      | Eq => compare_mn_1 m xl y 
      | r  => Gt
      end
    end
  end.

End CompareRec.



