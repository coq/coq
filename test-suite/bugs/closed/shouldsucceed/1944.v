(* Test some uses of ? in introduction patterns *)

Inductive J : nat -> Prop :=
  | K : forall p, J p -> (True /\ True)  -> J (S p).

Lemma bug : forall n, J n -> J (S n).
Proof.
  intros ? H.
  induction H as [? ? [? ?]].
