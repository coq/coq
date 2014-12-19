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

Lemma deep2 : v1 = v2.
Proof using v1 v2.
Admitted.

End S2.

Check (deep 3 : v1 = 3).
Check (deep2 3 : v1 = 3).

End S1.

Check (deep 3 4 : 3 = 4).
Check (deep2 3 4 : 3 = 4).


Section P1.

Variable x : nat.
Variable y : nat.
Variable z : nat.


Collection TOTO := x y.

Collection TITI := TOTO - x.

Lemma t1 : True. Proof using TOTO. trivial. Qed.
Lemma t2 : True. Proof using TITI. trivial. Qed.

 Section P2.
 Collection TOTO := x.
 Lemma t3 : True. Proof using TOTO. trivial. Qed.
 End P2.

Lemma t4 : True. Proof using TOTO. trivial. Qed.

End P1.

Lemma t5 : True. Fail Proof using TOTO. trivial. Qed.

Check (t1 1 2 : True).
Check (t2 1 : True).
Check (t3 1 : True).
Check (t4 1 2 : True).


Section T1.

Variable x : nat.
Hypothesis px : 1 = x.
Let w := x + 1.

Set Suggest Proof Using.

Set Default Proof Using "Type".

Lemma bla : 2 = w.
Proof.
admit.
Qed.

End T1.

Check (bla 7 : 2 = 8).



