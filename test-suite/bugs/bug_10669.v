Parameter (A0:Type) (B0:A0).
Definition foo0 := B0.

Set Universe Polymorphism.
Parameter (A1:Type) (B1:A1).
Definition foo1 := B1.

Section S.
  Context (A2:Type) (B2:A2).
  Definition foo2 := B2.
End S.
