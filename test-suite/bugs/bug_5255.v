Section foo.
  Context (x := 1).
  Definition foo : x = 1 := eq_refl.
End foo.

Module Type Foo.
  #[local] Definition x := 1.
  Definition foo : x = 1 := eq_refl.
End Foo.

Set Universe Polymorphism.

Inductive unit := tt.
Inductive eq {A} (x y : A) : Type := eq_refl : eq x y.

Section bar.
  Context (x := tt).
  Definition bar : eq x tt := eq_refl _ _.
End bar.

Module Type Bar.
  #[local] Definition x := tt.
  Definition bar : eq x tt := eq_refl _ _.
End Bar.
