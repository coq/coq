Polymorphic Record foo@{s;u|} (x : Type@{s;u}) := {}.

Set Universe Polymorphism.

Module Type A. Axiom A@{i} : Type@{i}. Axiom B : foo A. End A.
Module B <: A. Axiom A@{i} : Prop. Axiom B : foo A. Fail End B.

(*
Set Universe Polymorphism.

Module Irrel.
Polymorphic Record foo@{s;u|} (x : Univ@{s;u}) := {}.

Module Type A. Axiom A@{i} : Type@{i}. Axiom B@{i} : foo@{Type ; i} A@{i}. End A.
Module B <: A. Axiom A@{i} : Prop. Axiom B@{i} : foo@{Prop; i} A@{i}. End B.
End Irrel.


Module NotIrrel.
#[universes(polymorphic,cumulative=no)] Record foo@{s;u|} (x : Univ@{s;u}) := { }.

Unset Polymorphic Assumptions Cumulativity.

Module Type A. Axiom A@{i} : Type@{i}. Axiom B : foo A. End A.
Module B <: A. Axiom A@{i} : Prop. Axiom B : foo A. Fail End B.
Reset B. Axiom B@{j} : foo@{Type;j} A@{j}.  End B.
End NotIrrel.
*)