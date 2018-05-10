Definition idw (A : Type) := A.
Lemma foobar : unit.
Proof.
  Require Import Program.
  apply (const tt tt).
Qed.

Set Nested Proofs Allowed.

Lemma foobar' : unit.
  Lemma aux : forall A : Type, A -> unit.
  Proof. intros. pose (foo := idw A). exact tt. Show Universes. Qed.
  apply (@aux unit tt).
Qed.
