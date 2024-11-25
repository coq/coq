Unset Strict Universe Declaration.
Polymorphic Axiom foo@{u} : True.

Polymorphic Lemma bar : True /\ True.
Proof.
  split.
  shelve.

  par: exact foo@{i}.

  Unshelve.
  par: exact foo@{j}.
Defined.

Check bar@{_ _}.

Goal True.
  par: exact foo.
Qed.
