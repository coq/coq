Unset Universe Minimization ToSet.
Set Polymorphic Definitions Cumulativity.

Polymorphic Axiom tuple@{-i} : Type@{i} -> nat -> Type@{i}.

Record box := mkBox {
  elimBox: forall n: nat, tuple unit n -> bool;
}.

(* Set is indeed the principal type *)
Check box : Set.

(* This prevents putting the tuple in Set however *)
Record box'@{i} (A : Type@{i}) := mkBox' {
  elimBox': forall n: nat, tuple A n -> bool;
}.

Fail Check box' : Set -> Set.
