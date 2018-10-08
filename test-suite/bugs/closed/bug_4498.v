Require Export Coq.Unicode.Utf8.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Relations.Relation_Definitions.

Set Universe Polymorphism.

Reserved Notation "a ~> b" (at level 90, right associativity).

Class Category := {
  ob            : Type;
  uhom          := Type : Type;
  hom           : ob → ob → uhom where "a ~> b" := (hom a b);
  compose       : ∀ {A B C}, (B ~> C) → (A ~> B) → (A ~> C);
  equiv         : ∀ {A B}, relation (A ~> B);
  is_equiv      : ∀ {A B}, @Equivalence (A ~> B) equiv;
  comp_respects : ∀ {A B C},
      Proper (@equiv B C ==> @equiv A B ==> @equiv A C) (@compose A B C);
}.

Require Export Coq.Setoids.Setoid.

Add Parametric Morphism `{C : Category} {A B C} : (@compose _ A B C) with
  signature equiv ==> equiv ==> equiv as compose_mor.
Proof. apply comp_respects. Qed.
