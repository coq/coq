Require Setoid.

Declare Scope category_theory_scope.
Open Scope category_theory_scope.
Require Import Corelib.Classes.CMorphisms.
Set Primitive Projections.
Set Universe Polymorphism.

Class Setoid A := {
  equiv : crelation A;
  setoid_equiv :: Equivalence equiv
}.

Notation "f ≈ g" := (equiv f g) (at level 79) : category_theory_scope.

Reserved Infix "~>" (at level 90, right associativity).

Class Category := {
  obj : Type;

  hom : obj -> obj -> Type where "a ~> b" := (hom a b);
  homset :: forall X Y, Setoid (X ~> Y);

  id {x} : x ~> x;

}.

Delimit Scope category_scope with category.
Delimit Scope object_scope with object.

Notation "x ~> y" := (@hom _%category x%object y%object)
  (at level 90, right associativity) : homset_scope.

Coercion obj : Category >-> Sortclass.
Open Scope homset_scope.

Class Functor {C D : Category} := {
  fobj : C -> D;
  fmap {x y : C} (f : x ~> y) : fobj x ~> fobj y;

  fmap_respects :: forall x y, Proper (equiv ==> equiv) (@fmap x y);

  fmap_id {x : C} : fmap (@id C x) ≈ id;
}.
Declare Scope functor_type_scope.
Open Scope functor_type_scope.

Notation "C ⟶ D" := (@Functor C%category D%category)
  (at level 90, right associativity) : functor_type_scope.

#[export] Hint Rewrite @fmap_id : categories.

Ltac cat_simpl :=
  simpl; intros;
  autorewrite with categories;
  try reflexivity.

Obligation Tactic := cat_simpl.

Program Definition Compose {C D E : Category}
        (F : D ⟶ E) (G : C ⟶ D) : C ⟶ E := {|
  fobj := fun x => fobj (fobj x);
  fmap := fun _ _ f => fmap (fmap f)
|}.

Next Obligation.
Admitted.
