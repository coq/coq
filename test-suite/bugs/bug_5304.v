Parameter A : nat -> Prop.

Parameter H1 : A 1.
Parameter H2 : A 2.

Global Hint Resolve H1 | 1 : db1.
Global Hint Resolve H2 | 2 : db2.

Lemma foo : { n | A n }.
typeclasses eauto with core db2 db1.
Defined.

Check eq_refl : proj1_sig foo = 1.
