Unset Universe Minimization ToSet.
Polymorphic Axiom tuple@{i} : Type@{i} -> nat -> Type@{i}.

Record box := mkBox {
  elimBox: forall n: nat, tuple unit n -> bool;
}.

(* This prevents putting the tuple in Set however, just because Set < i  *)
Fail Check box : Set.

Module Poly.
Set Universe Polymorphism.
Record box' := mkBox' {
  elimBox': forall n: nat, tuple unit n -> bool;
}.
(* Set is indeed the principal type *)
Check box' : Set.
End Poly.
Module PolyParam.
Set Universe Polymorphism.
(* This does not prevent putting the tuple in Set in univ poly mode *)
Record box'@{i} (A : Type@{i}) := mkBox' {
  elimBox': forall n: nat, tuple A n -> bool;
}.

Check box' : Set -> Set.
End PolyParam.
