Set Primitive Projections.
Set Implicit Arguments.
Set Universe Polymorphism.
Set Asymmetric Patterns.

Inductive sum A B := inl : A -> sum A B | inr : B -> sum A B.
Inductive Empty :=.

Record category :=
  { ob :> Type;
    hom : ob -> ob -> Type
  }.
Set Printing All.
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
Fail exact (hom x y). (* Toplevel input, characters 26-27:
Error:
In environment
C : category
D : category
x : sum (ob C) (ob D)
y : sum (ob C) (ob D)
The term "x" has type "sum (ob C) (ob D)" while it is expected to have type
 "ob ?16". *)
