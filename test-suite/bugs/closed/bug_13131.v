Set Mangle Names.

Class A := {}.

Lemma foo `{A} : A.
Proof. Fail exact H. assumption. Qed.
