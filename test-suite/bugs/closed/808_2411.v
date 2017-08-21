Section test.
Variable n:nat.
Lemma foo: 0 <= n.
Proof.
(* declaring an Axiom during a proof makes it immediatly
   usable, juste as a full Definition. *)
Axiom bar : n = 1.
rewrite bar.
now apply le_S.
Qed.

Lemma foo' : 0 <= n.
Proof.
(* Declaring an Hypothesis during a proof is ok,
   but this hypothesis won't be usable by the current proof(s),
   only by later ones. *)
Hypothesis bar' : n = 1.
Fail rewrite bar'.
Abort.

Lemma foo'' : 0 <= n.
Proof.
rewrite bar'.
now apply le_S.
Qed.

End test.
