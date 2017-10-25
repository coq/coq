Require Import Setoid.

Parameter P : nat -> Prop.
Parameter Q : nat -> Prop.
Parameter PQ : forall n, P n <-> Q n.

Lemma PQ2 : forall n, P n -> Q n.
  intros.
  rewrite PQ in H.
  trivial.
Qed.

