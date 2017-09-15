Set Primitive Projections.
Set Implicit Arguments.
Set Universe Polymorphism.
Set Asymmetric Patterns.
Set Printing Projections.
Inductive sum A B := inl : A -> sum A B | inr : B -> sum A B.
Inductive Empty :=.

Record category :=
  { ob :> Type;
    hom : ob -> ob -> Type
  }.

Definition sum_category (C D : category) : category :=
  {|
    ob := sum (ob C) (ob D);
    hom x y := match x, y with
                 | inl x, inl y => @hom C x y
                 | inr x, inr y => @hom D x y
                 | _, _ => Empty
               end |}.

Goal forall C D (x y : ob (sum_category C D)), Type.
intros C D x y.
hnf in x, y.
exact (hom (sum_category _ _) x y). 
Defined.
