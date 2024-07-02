Section S.
Variable x : nat.
Lemma foo : nat. Admitted.
Lemma bar : nat. clear x. Admitted.
End S.

Check foo : nat.
Check bar : nat.
