Require Export Stdlib.Classes.Morphisms.
Require Export Stdlib.Relations.Relation_Definitions.
Require Export Stdlib.Setoids.Setoid.

Set Universe Polymorphism.

Reserved Notation "a ~> b" (at level 90, right associativity).

Class Category := {
  ob            : Type;
  uhom          := Type : Type;
  hom           : ob -> ob -> uhom where "a ~> b" := (hom a b);
  compose       : forall {A B C}, (B ~> C) -> (A ~> B) -> (A ~> C);
  equiv         : forall {A B}, relation (A ~> B);
  is_equiv      : forall {A B}, @Equivalence (A ~> B) equiv;
  comp_respects : forall {A B C},
      Proper (@equiv B C ==> @equiv A B ==> @equiv A C) (@compose A B C);
}.

Add Parametric Morphism `{Category} {A B C} : (@compose _ A B C) with
  signature equiv ==> equiv ==> equiv as compose_mor.
Proof. apply comp_respects. Qed.
