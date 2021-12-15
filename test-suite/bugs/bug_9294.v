Set Printing Universes.

Inductive Foo@{i} (A:Type@{i}) : Type := foo : (Set:Type@{i}) -> Foo A.
Arguments foo {_} _.
Print Universes Subgraph (Foo.i).
Definition bar : Foo True -> Set := fun '(foo x) => x.

Definition foo_bar (n : Foo True) : foo (bar n) = n.
Proof. destruct n;reflexivity. Qed.

Definition bar_foo (n : Set) : bar (foo n) = n.
Proof. reflexivity. Qed.

Require Import Hurkens.

Inductive box (A : Set) : Prop := Box : A -> box A.

Definition Paradox : False.
Proof.
Fail unshelve refine (
  NoRetractFromSmallPropositionToProp.paradox
  (Foo True)
  (fun A => foo A)
  (fun A => box (bar A))
  _
  _
  False
).
Abort.
