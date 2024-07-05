Require Program.Basics Program.Tactics.
Require Stdlib.Classes.CMorphisms.
Require Setoid.

Export Program.Basics Program.Tactics.
Delimit Scope category_theory_scope with category_theory.
Open Scope category_theory_scope.
Export Stdlib.Classes.CMorphisms.

Notation "∀  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) :
  category_theory_scope.

Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity): category_theory_scope.

Class Setoid A := {
  equiv : crelation A;
  setoid_equiv :: Equivalence equiv
}.

Notation "f ≈ g" := (equiv f g) (at level 79) : category_theory_scope.

Reserved Infix "~>" (at level 90, right associativity).

Class Category := {
  obj : Type;

  uhom := Type : Type;
  hom : obj -> obj -> uhom where "a ~> b" := (hom a b);
  homset :: ∀ X Y, Setoid (X ~> Y);

  id {x} : x ~> x;
  compose {x y z} (f: y ~> z) (g : x ~> y) : x ~> z
    where "f ∘ g" := (compose f g);

  compose_respects x y z ::
    Proper (equiv ==> equiv ==> equiv) (@compose x y z);

  dom {x y} (f: x ~> y) := x;
  cod {x y} (f: x ~> y) := y;

  id_left  {x y} (f : x ~> y) : id ∘ f ≈ f;
  id_right {x y} (f : x ~> y) : f ∘ id ≈ f;

  comp_assoc {x y z w} (f : z ~> w) (g : y ~> z) (h : x ~> y) :
    f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h;
  comp_assoc_sym {x y z w} (f : z ~> w) (g : y ~> z) (h : x ~> y) :
    (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)
}.

Delimit Scope category_scope with category.
Delimit Scope object_scope with object.
Delimit Scope morphism_scope with morphism.

Notation "x ~> y" := (@hom _%category x%object y%object)
  (at level 90, right associativity) : homset_scope.

Notation "f ∘ g" :=
  (@compose _%category _%object _%object _%object f%morphism g%morphism)
  : morphism_scope.

Coercion obj : Category >-> Sortclass.

Open Scope category_scope.
Open Scope homset_scope.
Open Scope morphism_scope.

#[warning="context-outside-section"] Context {C : Category}.

Class Isomorphism (x y : C) : Type := {
  to   :: x ~> y;
  from :  y ~> x;

  iso_to_from : to ∘ from ≈ id;
  iso_from_to : from ∘ to ≈ id
}.

Arguments to {x y} _.
Arguments from {x y} _.
Arguments iso_to_from {x y} _.
Arguments iso_from_to {x y} _.

Infix "≅" := Isomorphism (at level 91) : category_scope.

Global Program Instance iso_id {x : C} : x ≅ x := {
  to   := id;
  from := id
}.
Next Obligation.
  now rewrite id_left.
Qed.
Next Obligation.
  now rewrite id_left.
Qed.

Global Program Definition iso_sym {x y : C} `(f : x ≅ y) : y ≅ x := {|
  to   := from f;
  from := to f;

  iso_to_from := iso_from_to f;
  iso_from_to := iso_to_from f
|}.

Global Program Definition iso_compose {x y z : C} `(f : y ≅ z) `(g : x ≅ y) :
  x ≅ z := {|
  to   := to f ∘ to g;
  from := from g ∘ from f
|}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (to g)).
  rewrite iso_to_from.
  rewrite id_left.
  apply iso_to_from.
Defined.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (from f)).
  rewrite iso_from_to.
  rewrite id_left.
  apply iso_from_to.
Defined.

Global Program Instance isomorphism_equivalence : Equivalence Isomorphism := {
  Equivalence_Reflexive  := @iso_id;
  Equivalence_Symmetric  := @iso_sym;
  Equivalence_Transitive := fun _ _ _ g f => iso_compose f g
}.

Lemma iso_compose' {x y z : C} `(f : y ≅ z) `(g : x ≅ y) : x ≅ z.
Proof.
  rewrite g.
Abort.
