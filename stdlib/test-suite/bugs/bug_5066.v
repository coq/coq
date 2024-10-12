Require Import Vector.

Fail Program Fixpoint vector_rev {A : Type} {n1 n2 : nat} (v1 : Vector.t A n1) (v2 : Vector.t A n2) : Vector.t A (n1+n2) :=
  match v1 with
  | nil _          => v2
  | cons _ e n' sv => vector_rev sv (cons A e n2 v2)
  end.
