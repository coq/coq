Inductive trinat (n:nat): nat -> nat -> Prop := r : trinat n n n.

Polymorphic Axiom n@{u}: nat.

Lemma foo@{u v} : trinat n@{u} n@{v} n@{v}.
Proof.
  set (m := n).
  apply r.
Qed.
