Polymorphic Axiom foo@{u} : True.

Polymorphic Lemma bar : True /\ True.
Proof.
  split.
  shelve.

  par: exact foo.

  Unshelve.
  par: exact foo.
Defined.

Check bar@{_ _}.

Goal True.
  par: exact foo.
Qed.
