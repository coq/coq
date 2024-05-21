Set Universe Polymorphism.

Inductive eq@{s|u|} (A:Type@{s|u}) (x:A) : A -> Prop :=
  eq_refl : eq A x x.

Inductive bool@{s| |} : Type@{s|Set} := true | false.

Lemma foo@{s| |} : forall (b : bool@{s|}),
    eq _ b true ->
    eq _ match b with
    | true => b
    | false => b end b.
Proof.
  intros b H.
  rewrite H.
  reflexivity.
Qed.
