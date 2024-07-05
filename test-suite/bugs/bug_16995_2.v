Require Export Stdlib.Program.Basics.
Require Setoid.

Require Export Stdlib.Classes.CMorphisms.

Declare Scope category_theory_scope.
Open Scope category_theory_scope.

Notation "∀  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) :
  category_theory_scope.

Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity): category_theory_scope.
Notation "x ↔ y" := (iffT x y)
  (at level 95, no associativity) : category_theory_scope.

Infix "∧" := prod (at level 80, right associativity) : category_theory_scope.

Notation "'λ'  x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity) :
  category_theory_scope.
Set Universe Polymorphism.

Class Setoid A := {
  equiv : crelation A;
  setoid_equiv : Equivalence equiv
}.
#[export] Existing Instance setoid_equiv.

Notation "f ≈ g" := (equiv f g) (at level 79) : category_theory_scope.

Reserved Infix "~>" (at level 90, right associativity).

Class Category@{o h p | h <= p} : Type@{max(o+1,h+1,p+1)} := {
  obj : Type@{o};

  hom : obj → obj → Type@{h} where "a ~> b" := (hom a b);
  homset : ∀ X Y, Setoid@{h p} (X ~> Y);

  id {x} : x ~> x;
  compose {x y z} (f: y ~> z) (g : x ~> y) : x ~> z
    where "f ∘ g" := (compose f g);

  compose_respects {x y z} :
    Proper@{h p} (respectful@{h p h p h p} equiv
                    (respectful@{h p h p h p} equiv equiv))
      (@compose x y z);

  id_left  {x y} (f : x ~> y) : id ∘ f ≈ f;
  id_right {x y} (f : x ~> y) : f ∘ id ≈ f;

}.
#[export] Existing Instance homset.
#[export] Existing Instance compose_respects.

Delimit Scope category_scope with category.
Delimit Scope object_scope with object.
Delimit Scope morphism_scope with morphism.

Notation "x ~> y" := (@hom _%category x%object y%object)
  (at level 90, right associativity) : homset_scope.

Notation "f ∘ g" :=
  (@compose _%category _%object _%object _%object f%morphism g%morphism)
  : morphism_scope.

Coercion obj : Category >-> Sortclass.

#[export] Hint Rewrite @id_left : categories.
#[export] Hint Rewrite @id_right : categories.
Open Scope homset_scope.
Open Scope morphism_scope.

Class Functor@{o1 h1 p1 o2 h2 p2}
  {C : Category@{o1 h1 p1}} {D : Category@{o2 h2 p2}} := {
  fobj : C → D;
  fmap {x y : C} (f : x ~> y) : fobj x ~> fobj y;

  fmap_id {x : C} : fmap (@id C x) ≈ id;
}.
Declare Scope functor_type_scope.
Delimit Scope functor_scope with functor.
Open Scope functor_type_scope.

Coercion fobj : Functor >-> Funclass.

Notation "C ⟶ D" := (@Functor C%category D%category)
  (at level 90, right associativity) : functor_type_scope.
Notation "fmap[ F ]" := (@fmap _ _ F%functor _ _)
  (at level 9, format "fmap[ F ]") : morphism_scope.

#[export] Hint Rewrite @fmap_id : categories.

Generalizable All Variables.

Section Transform.

Universes o1 h1 p1 o2 h2 p2.
Context {C : Category@{o1 h1 p2}}.
Context {D : Category@{o2 h2 p2}}.
Context {F : C ⟶ D}.
Context {G : C ⟶ D}.

Class Transform := {
  transform {x} : F x ~> G x;

  naturality {x y} (f : x ~> y) :
    fmap[G] f ∘ transform ≈ transform ∘ fmap[F] f;

  naturality_sym {x y} (f : x ~> y) :
    transform ∘ fmap[F] f ≈ fmap[G] f ∘ transform
}.

End Transform.

#[export] Hint Extern 4 (equiv ?A ?A) => reflexivity : category_laws.

Ltac cat :=
  autorewrite with categories;
  auto with category_laws.

Ltac cat_simpl :=
  intros;
  simpl in *; cat.

#[global] Obligation Tactic := idtac.

Program Definition nat_id `{F : C ⟶ D} : @Transform _ _ F F :=
  {| transform := λ X, fmap (@id C X) |}.

Solve Obligations with cat_simpl.
