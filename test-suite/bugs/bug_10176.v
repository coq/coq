Class Foo (xxx:nat) := foo : nat.

Lemma aa `{Foo} : nat. Abort.

Fail Lemma xy (Foo:bool->Type) `{Foo} : nat.

Fail Lemma yx (Fooo:bool->Type) `{Fooo} : nat.
