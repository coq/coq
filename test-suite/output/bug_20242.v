Polymorphic Record foo@{s|u|} (x : Type@{s|u}) := {}.
Inductive sEmpty : SProp := .
Module Type A. Axiom A : Type. Axiom B : foo A. End A.
Unset Universe Checking.
Module B <: A. Axiom A : SProp. Axiom B : foo A. Fail End B.
