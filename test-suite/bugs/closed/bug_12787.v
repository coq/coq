Inductive sigT3 {A: Type} {P: A -> Type} (Q: forall a: A, P a -> Type) :=
  existT3: forall a: A, forall b: P a, Q a b -> sigT3 Q
.

Definition projT3_1 {A: Type} {P: A -> Type} {Q: forall a: A, P a -> Type} (a: sigT3 Q) :=
  let 'existT3 _ x0 _ _ := a in x0.

Definition projT3_2 {A: Type} {P: A -> Type} {Q: forall a: A, P a -> Type} (a: sigT3 Q) : P (projT3_1 a) :=
  let 'existT3 _ x0 x1 _ := a in x1.



Lemma projT3_3_eq' (A B: Type) (Q: B -> Type) (a b: sigT3 (fun (_: A) b => Q b)) (H: a = b) :
  unit.
Proof.
  destruct a as [x0 x1 x2], b as [y0 y1 y2].
  assert (H' := f_equal projT3_1 H).
  cbn in H'.
  subst x0.
  assert (H' := f_equal (projT3_2 (P := fun _ => B)) H).
  cbn in H'.
  subst x1.

  injection H as H'.
  exact tt.
Qed.
