
Module X.
  (*Set Universe Polymorphism.*)
  Inductive paths A (x : A) : forall _ : A, Type := idpath : paths A x x.
  Notation "x = y" := (@paths _ x y) (at level 70, no associativity) : type_scope.

  Axioms A B : Type.
  Axiom P : A = B.
  Definition foo : A = B.
    abstract (rewrite <- P; reflexivity).
  Defined.
End X.

Module Y.
  (*Set Universe Polymorphism.*)
  Inductive paths A (x : A) : forall _ : A, Type := idpath : paths A x x.
  Notation "x = y" := (@paths _ x y) (at level 70, no associativity) : type_scope.

  Axioms A B : Type.
  Axiom P : A = B.
  Definition foo : (A = B) * (A = B).
    split; abstract (rewrite <- P; reflexivity).
  Defined.
End Y.
