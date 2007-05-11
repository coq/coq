Require Import ZArith.
Require Import Basic_type.


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
  | 0 => compare0_m 
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
  | 0 => compare_m 
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



