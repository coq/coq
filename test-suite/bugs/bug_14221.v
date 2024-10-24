Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Require Stdlib.Program.Basics Stdlib.Program.Tactics.
Export Stdlib.Program.Basics Stdlib.Program.Tactics.
Set Primitive Projections.
Set Universe Polymorphism.

Close Scope nat_scope.
Require Setoid.
Require Export Stdlib.Classes.CMorphisms.

Notation "∀  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity).

Class Setoid A := {
  equiv : crelation A;
  setoid_equiv :: Equivalence equiv
}.

Notation "f ≈ g" := (equiv f g) (at level 79).

Ltac cat :=
  intros;
  autorewrite with categories;
  auto with category_laws;
  try reflexivity.

#[export] Hint Extern 4 (equiv ?A ?A) => reflexivity : category_laws.

Ltac proper := repeat intro; simpl; try cat; intuition.

Ltac cat_simpl :=
  program_simpl; autounfold;
  try solve [
    program_simpl; autounfold in *;
    simpl in *; intros;
    simpl in *; cat];
  simpl in *.

Global Obligation Tactic := cat_simpl.

Reserved Infix "~>" (at level 90, right associativity).

Class Category := {
  obj : Type;

  uhom := Type : Type;
  hom : obj -> obj -> uhom where "a ~> b" := (hom a b);
  homset :: ∀ X Y, Setoid (X ~> Y);

  id {x} : x ~> x;
}.

Delimit Scope category_scope with category.
Delimit Scope object_scope with object.

Notation "x ~> y" := (@hom _%category x%object y%object)
  (at level 90, right associativity) : homset_scope.
Notation "x ~{ C }~> y" := (@hom C%category x%object y%object)
  (at level 90) : homset_scope.

Notation "id[ x ]" := (@id _%category x%object)
  (at level 9, format "id[ x ]") : morphism_scope.

Coercion obj : Category >-> Sortclass.

Open Scope homset_scope.
Open Scope morphism_scope.

Class Functor (C D : Category) := {
  fobj : C -> D;
  fmap {x y : C} (f : x ~> y) : fobj x ~> fobj y;

  fmap_respects :: ∀ x y, Proper (equiv ==> equiv) (@fmap x y);

  fmap_id {x : C} : fmap (@id C x) ≈ id;
}.
Delimit Scope functor_scope with functor.

Coercion fobj : Functor >-> Funclass.

Notation "fmap[ F ]" := (@fmap _ _ F%functor _ _)
  (at level 9, format "fmap[ F ]") : morphism_scope.

#[export] Hint Rewrite @fmap_id : categories.

Definition Product (C D : Category) : Category := {|
  obj     := C * D;
  hom     := fun x y => (fst x ~> fst y) * (snd x ~> snd y);
  homset  := fun x y =>
    let setoid_C := @homset C (fst x) (fst y) in
    let setoid_D := @homset D (snd x) (snd y) in
    {| equiv := fun f g =>
         (@equiv _ setoid_C (fst f) (fst g) *
          @equiv _ setoid_D (snd f) (snd g))
     ; setoid_equiv := _
         {| Equivalence_Reflexive  := fun x =>
              (@Equivalence_Reflexive _ _ (@setoid_equiv _ setoid_C) (fst x),
               @Equivalence_Reflexive _ _ (@setoid_equiv _ setoid_D) (snd x))
          ; Equivalence_Symmetric  := fun x y f =>
              (@Equivalence_Symmetric
                 _ _ (@setoid_equiv _ setoid_C) (fst x) (fst y) (fst f),
               @Equivalence_Symmetric
                 _ _ (@setoid_equiv _ setoid_D) (snd x) (snd y) (snd f))
          ; Equivalence_Transitive := fun x y z f g =>
              (@Equivalence_Transitive
                 _ _ (@setoid_equiv _ setoid_C) (fst x) (fst y) (fst z)
                 (fst f) (fst g),
               @Equivalence_Transitive
                 _ _ (@setoid_equiv _ setoid_D) (snd x) (snd y) (snd z)
                 (snd f) (snd g)) |} |};
  id      := fun _ => (id, id);
|}.

Section Bifunctor.

Context {C : Category}.
Context {D : Category}.
Context {E : Category}.

Definition bimap {F : Functor (Product C D) E} {x w : C} {y z : D}
           (f : x ~{C}~> w) (g : y ~{D}~> z) :
  F (x, y) ~{E}~> F (w, z) := @fmap (Product C D) E F (x, y) (w, z) (f, g).

Global Program Instance bimap_respects {F : Functor (Product C D) E} {x w : C} {y z : D} :
  Proper (equiv ==> equiv ==> equiv) (@bimap F x w y z).
Next Obligation.
admit.
Defined.

Lemma bimap_id_id {F : Functor (Product C D) E} {x y} :
  bimap (id[x]) (id[y]) ≈ id.
admit.
Defined.

End Bifunctor.

Notation "bimap[ F ]" := (@bimap _ _ _ F%functor _ _ _ _)
  (at level 9, format "bimap[ F ]") : morphism_scope.

#[export] Hint Rewrite @bimap_id_id : categories.

Reserved Infix "⨂" (at level 30, right associativity).

Class Monoidal {C : Category} := {
  tensor : Functor (Product C C) C where "x ⨂ y" := (tensor (x, y));
}.

Notation "x ⨂ y" := (@tensor _ _ (x%object, y%object))
  (at level 30, right associativity) : object_scope.
Notation "f ⨂ g" := (bimap[@tensor _ _] f g)
  (at level 30, right associativity) : morphism_scope.

#[export] Program Instance PP
        {C : Category} {D : Category} `{@Monoidal D}
        {F : Functor C D} {G : Functor C D} : Functor C D := {
  fobj := fun x => (F x ⨂ G x)%object;
  fmap := fun _ _ f => fmap[F] f ⨂ fmap[G] f
}.
Next Obligation.
  proper.
  rewrite X. (* was anomaly undefined universe *)
  reflexivity.
Qed.
