Set Primitive Projections.
Set Implicit Arguments.
Record prod A B := pair { fst : A ; snd : B }.
Goal forall A B : Set, True.
Proof.
  intros A B.
  evar (a : prod A B); evar (f : (prod A B -> Set)).
  let a' := (eval unfold a in a) in
  set(foo:=eq_refl : a' = (@pair _ _ (fst a') (snd a'))).
