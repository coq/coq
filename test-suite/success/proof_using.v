Section Foo.

Variable a : nat.

Lemma l1 : True.
Fail Proof using non_existing.
Proof using a.
exact I.
Qed.

Lemma l2 : True.
Proof using a.
Admitted.

Lemma l3 : True.
Proof using a.
admit.
Qed.

End Foo.

Check (l1 3).
Check (l2 3).
Check (l3 3).

Section Bar.

Variable T : Type.
Variable a b : T.
Variable H : a = b.

Lemma l4 : a = b.
Proof using H.
exact H.
Qed.

End Bar.

Check (l4 _ 1 1 _ : 1 = 1).

Section S1.

Variable v1 : nat.

Section S2.

Variable v2 : nat.

Lemma deep : v1 = v2.
Proof using v1 v2.
admit.
Qed.

End S2.

Check (deep 3 : v1 = 3).

End S1.

Check (deep 3 4 : 3 = 4).

