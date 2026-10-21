Set Universe Polymorphism.

Module Irrel.
Polymorphic Record foo@{s;u|} (x : Univ@{s;u}) := {}.

Module Type A. Axiom A@{i} : Type@{i}. Axiom B : foo A. End A.
Module B <: A. Axiom A@{i} : Prop. Axiom B : foo A. End B.
End Irrel.


Module NotIrrel.
#[universes(polymorphic,cumulative=no)] Record foo@{s;u|} (x : Univ@{s;u}) := { }.

Unset Polymorphic Assumptions Cumulativity.

Module Type A. Axiom A@{i} : Type@{i}. Axiom B : foo A. End A.
Module B <: A. Axiom A@{i} : Prop. Axiom B : foo A. Fail End B.
Reset B. Axiom B@{j} : foo@{Type;j} A@{j}. End B.
End NotIrrel.
