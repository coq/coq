Require Import ssreflect.

Set Universe Polymorphism.

Cumulative Variant paths {A} (x:A) : A -> Type
  := idpath : paths x x.

Register paths as core.eq.type.
Register idpath as core.eq.refl.

Lemma case_test (b:bool) : paths b b.
Proof. case B:b; reflexivity. Qed.
