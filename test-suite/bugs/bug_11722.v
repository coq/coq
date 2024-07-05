Require Import Program.Basics Program.Tactics.
Set Universe Polymorphism.

Inductive paths@{i} (A : Type@{i}) (a : A) : A -> Type@{i} :=
  idpath : paths A a a.

Inductive nat :=
  | O : nat
  | S : nat -> nat.

Axiom cheat : forall {A}, A.

Program Definition foo@{i} : forall x : nat, paths@{i} nat x x := _.
Next Obligation.
  destruct x.
  constructor.
  apply cheat.
Defined. (* FIXED: Universe unbound error *)

Check foo@{_}.
