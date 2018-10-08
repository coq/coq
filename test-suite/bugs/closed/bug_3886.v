Require Import Program.

Inductive Even : nat -> Prop :=
| evenO : Even O
| evenS : forall n, Odd n -> Even (S n)
with Odd : nat -> Prop :=
| oddS : forall n, Even n -> Odd (S n).

Program Fixpoint doubleE {n} (e : Even n) : Even (2 * n)
  := _
with doubleO {n} (o : Odd n) : Odd (S (2 * n))
     := _.
Obligations.
Axiom cheat : forall {A}, A.
Obligation 1 of doubleE.
apply cheat.
Qed.

Obligation 1 of doubleO.
apply cheat.
Qed.

Check doubleE.
