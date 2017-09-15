Require Import Relations.

Record Poset{A:Type}(Le : relation A) : Type :=
  Build_Poset
  {
    Le_refl : forall x : A, Le x x;
    Le_trans : forall x y z : A, Le x y -> Le y z -> Le x z;
    Le_antisym : forall x y : A, Le x y -> Le y x -> x = y }.

Definition nat_Poset : Poset Peano.le.
Admitted.
