Axiom hp : Set.
Axiom cont : nat -> hp -> Prop.
Axiom sconj : (hp -> Prop) -> (hp -> Prop) -> hp -> Prop.
Axiom sconjImpl : forall h A B,
  (sconj A B) h -> forall (A' B': hp -> Prop),
    (forall h', A h' -> A' h') ->
    (forall h', B h' -> B' h') ->
    (sconj A' B') h.

Definition cont' (h:hp) := exists y, cont y h.

Lemma foo : forall h x y A,
  (sconj (cont x) (sconj (cont y) A)) h ->
  (sconj cont' (sconj cont' A)) h.
Proof.
  intros h x y A H.
  eapply sconjImpl.
  2:intros h' Hp'; econstructor; apply Hp'.
  2:intros h' Hp'; eapply sconjImpl.
  3:intros h'' Hp''; econstructor; apply Hp''.
  3:intros h'' Hp''; apply Hp''.
  2:apply Hp'.
  clear H.
Admitted.
