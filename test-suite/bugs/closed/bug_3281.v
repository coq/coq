Lemma foo_ : @eq _ nat Type. Admitted.
Fail Lemma foo : @eq Set nat Type.

Lemma foo : @eq Type nat Type. Admitted.
Lemma foo' : @eq _ Type nat. Admitted.
