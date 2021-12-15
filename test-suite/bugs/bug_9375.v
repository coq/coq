Set Primitive Projections.

Record toto : Type := Toto {
  toto1 : Type;
  toto2 : toto1 -> Type
}.

Record tata := Tata {
  tata1 : Type
}.

Canonical Structure tata_toto (x : toto) X :=
  Tata (toto2 x X).

Check fun (T : toto) (t : toto1 T) =>
   (eq_refl _ : @tata1 _ = @toto2 _ t).
