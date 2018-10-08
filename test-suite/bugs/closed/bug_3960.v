Require Program.Tactics.

Axiom foo : nat -> Prop.

Axiom fooP : forall n, foo n.

Class myClass (A: Type) :=
  {
    bar : A -> Prop
  }.

Program Instance myInstance : myClass nat :=
  {
    bar := foo
  }.

Class myClassP (A : Type)  :=
  {
    super :> myClass A;
    barP : forall (a : A), bar a
  }.

Instance myInstanceP : myClassP nat :=
  {
    barP := fooP
  }.
