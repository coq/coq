Unset Universe Minimization ToSet.

Cumulative Polymorphic Axiom tuple@{-i} : Type@{i} -> nat -> Type@{i}.

Record box := mkBox {
  elimBox: forall n: nat, tuple unit n -> bool;
}.

(* Set is indeed the principal type *)
Check box : Set.

Module NotPoly.
(* This prevents putting the tuple in Set however, just because Set < i  *)
Record box'@{i} (A : Type@{i}) := mkBox' {
  elimBox': forall n: nat, tuple A n -> bool;
}.

Fail Check box' : Set -> Set.
End NotPoly.
Module Poly.
Set Universe Polymorphism.
(* This does not prevent putting the tuple in Set in univ poly mode *)
Record box'@{i} (A : Type@{i}) := mkBox' {
  elimBox': forall n: nat, tuple A n -> bool;
}.

Check box' : Set -> Set.
End Poly.
