Declare ML Module "evil_plugin".

Universes i j.

Lemma foo@{} : Type@{j}.
Proof.
  magic i j; transparent_abstract exact_no_check Type@{i}.
Defined.

Definition bar : Type@{i} := Type@{j}.
