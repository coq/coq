Section Test.

Variables (A B : Type) (a : A) (b : B).
Variable c : A -> B.
Coercion c : A >-> B.

Notation COERCION := (c).

Check b = a.
End Test.
