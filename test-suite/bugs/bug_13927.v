Unset Universe Minimization ToSet.

Polymorphic Axiom tuple@{i} : Type@{i} -> nat -> Type@{i}.

Record box := mkBox {
  elimBox: forall n: nat, tuple unit n -> bool;
}.

Fail Check box : Set.
