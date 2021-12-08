Set Implicit Arguments.
Set Universe Polymorphism.

Module success.
  Unset Primitive Projections.

  Record category :=
    { ob : Type;
      hom : ob -> ob -> Type;
      comp : forall x y z, hom y z -> hom x y -> hom x z }.

  Delimit Scope hom_scope with hom.
  Bind Scope hom_scope with hom.
  Arguments hom : clear implicits.
  Arguments comp _ _ _ _ _%hom _%hom : clear implicits.

  Notation "f 'o' g" := (comp _ _ _ _ f g) (at level 40, left associativity) : hom_scope.

  Record functor (C D : category) :=
    { ob_of : ob C -> ob D;
      hom_of : forall x y, hom C x y -> hom D (ob_of x) (ob_of y) }.

  Delimit Scope functor_scope with functor.
  Bind Scope functor_scope with functor.

  Arguments hom_of _ _ _%functor _ _ _%hom.

  Notation "F '_1' m" := (hom_of F _ _ m) (at level 10, no associativity) : hom_scope.

  Axiom f_comp : forall C D E, functor D E -> functor C D -> functor C E.
  Notation "f 'o' g" := (@f_comp _ _ _ f g) (at level 40, left associativity) : functor_scope.

  Check ((_ o _) _1 _)%hom. (* ((?16 o ?17) _1 ?20)%hom
     : hom ?15 (ob_of (?16 o ?17) ?18) (ob_of (?16 o ?17) ?19) *)
End success.

Module failure.
  Set Primitive Projections.

  Record category :=
    { ob : Type;
      hom : ob -> ob -> Type;
      comp : forall x y z, hom y z -> hom x y -> hom x z }.

  Delimit Scope hom_scope with hom.
  Bind Scope hom_scope with hom.
  Arguments hom : clear implicits.
  Arguments comp _ _ _ _ _%hom _%hom : clear implicits.

  Notation "f 'o' g" := (comp _ _ _ _ f g) (at level 40, left associativity) : hom_scope.

  Record functor (C D : category) :=
    { ob_of : ob C -> ob D;
      hom_of : forall x y, hom C x y -> hom D (ob_of x) (ob_of y) }.

  Delimit Scope functor_scope with functor.
  Bind Scope functor_scope with functor.

  Arguments hom_of _ _ _%functor _ _ _%hom.

  Notation "F '_1' m" := (hom_of F _ _ m) (at level 10, no associativity) : hom_scope.
  Notation "F '_2' m" := (hom_of F%functor _ _ m) (at level 10, no associativity) : hom_scope.

  Axiom f_comp : forall C D E, functor D E -> functor C D -> functor C E.
  Notation "f 'o' g" := (@f_comp _ _ _ f g) (at level 40, left associativity) : functor_scope.

  Check ((_ o _) _2 _)%hom. (* ((?14 o ?15)%functor _1 ?18)%hom
     : hom ?13 (ob_of (?14 o ?15)%functor ?16)
         (ob_of (?14 o ?15)%functor ?17) *)
  Check ((_ o _) _1 _)%hom. (* Toplevel input, characters 7-19:
Error:
The term "(?23 o ?24)%hom" has type "hom ?19 ?20 ?22"
while it is expected to have type "functor ?25 ?26". *)
End failure.
