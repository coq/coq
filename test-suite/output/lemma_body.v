Lemma toto1 := 3.
Lemma toto2 : nat := 3.
Theorem toto3 A : A -> A := fun x : A => x.

Goal True.
unfold plus. (* we check that a non-occurring def is OK *)
Fail unfold toto1.
Fail unfold toto2.
Fail unfold toto3.

Fail Lemma titi1 : nat with titi2 : bool := 3.
Fail Lemma tata.
