From Stdlib Require Import SetoidList.

Lemma Problem : forall (A : Type) (eqA : A -> A -> Prop) (x : A) (l : list A), NoDupA eqA (x::l) -> True.
  Info 1 destruct 1.
Abort.
