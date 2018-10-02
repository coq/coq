Require Import Program.

Inductive Even : nat -> Prop :=
| evenO : Even O
| evenS : forall n, Odd n -> Even (S n)
with Odd : nat -> Prop :=
| oddS : forall n, Even n -> Odd (S n).
Axiom admit : forall {T}, T.
Program Fixpoint doubleE {n} (e : Even n) : Even (2 * n) := admit
with doubleO {n} (o : Odd n) : Odd (S (2 * n)) := _.
Next Obligation of doubleE.
