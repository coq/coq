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
                 | inl x, inl y => @hom _ x y (* Toplevel input, characters 177-178:
Error:
In environment
C : category
D : category
x : sum (ob C) (ob D)
y : sum (ob C) (ob D)
x0 : ob C
y0 : ob C
The term "x0" has type "ob C" while it is expected to have type
"ob ?6" (unable to find a well-typed instantiation for
"?6": cannot unify"Type" and "category"). *)
                 | inr x, inr y => @hom _ x y
                 | _, _ => Empty
               end |}.
