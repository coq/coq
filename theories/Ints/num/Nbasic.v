Require Import ZArith.
Require Import ZAux.
Require Import ZDivModAux.
Require Import Basic_type.
Require Import Max.

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

Open Scope nat_scope.

Fixpoint plusnS (n m: nat) {struct n} : (n + S m = S (n + m))%nat :=
  match n return  (n + S m = S (n + m))%nat with
  | 0 => refl_equal (S m)
  | S n1 =>
      let v := S (S n1 + m) in
      eq_ind_r (fun n => S n = v) (refl_equal v) (plusnS n1 m)
  end.

Fixpoint plusn0 n : n + 0 = n :=
  match n return (n + 0 = n) with
  | 0 => refl_equal 0
  | S n1 =>
      let v := S n1 in
      eq_ind_r (fun n : nat => S n = v) (refl_equal v) (plusn0 n1)
  end.

 Fixpoint diff (m n: nat) {struct m}: nat * nat :=
   match m, n with
     O, n => (O, n)
   | m, O => (m, O)
   | S m1, S n1 => diff m1 n1
   end.

Fixpoint diff_l (m n : nat) {struct m} : fst (diff m n) + n = max m n :=
  match m return fst (diff m n) + n = max m n with
  | 0 =>
      match n return (n = max 0 n) with
      | 0 => refl_equal _
      | S n0 => refl_equal _
      end
  | S m1 =>
      match n return (fst (diff (S m1) n) + n = max (S m1) n)
      with
      | 0 => plusn0 _
      | S n1 =>
          let v := fst (diff m1 n1) + n1 in
          let v1 := fst (diff m1 n1) + S n1 in
          eq_ind v (fun n => v1 = S n) 
            (eq_ind v1 (fun n => v1 = n) (refl_equal v1) (S v) (plusnS _ _))
            _ (diff_l _ _)
      end
  end.

Fixpoint diff_r (m n: nat) {struct m}: snd (diff m n) + m = max m n :=
  match m return (snd (diff m n) + m = max m n) with
  | 0 =>
      match n return (snd (diff 0 n) + 0 = max 0 n) with
      | 0 => refl_equal _
      | S _ => plusn0 _
      end
  | S m => 
      match n return (snd (diff (S m) n) + S m = max (S m) n) with
      | 0 => refl_equal (snd (diff (S m) 0) + S m)
      | S n1 =>
          let v := S (max m n1) in
          eq_ind_r (fun n => n = v)
            (eq_ind_r (fun n => S n = v)
               (refl_equal v) (diff_r _ _)) (plusnS _ _)
      end
  end.

 Variable w: Set.

 Definition castm (m n: nat) (H: m = n) (x: word w (S m)):
     (word w (S n)) :=
 match H in (_ = y) return (word w (S y)) with
 | refl_equal => x
 end.

Variable m: nat.
Variable v: (word w (S m)).

Fixpoint extend_tr (n : nat) {struct n}: (word w (S (n + m))) :=
  match n  return (word w (S (n + m))) with
  | O => v
  | S n1 => WW W0 (extend_tr n1)
  end.

End ExtendMax.

Implicit Arguments extend_tr[w m].
Implicit Arguments castm[w m n].



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



