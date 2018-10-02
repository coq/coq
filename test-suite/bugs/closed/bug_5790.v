Set Universe Polymorphism.
Section foo.
Context (v : Type).
Axiom a : True <-> False.

Hint Resolve -> a.
End foo.
