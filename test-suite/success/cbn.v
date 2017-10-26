(* cbn is able to refold mutual recursive calls *)

Fixpoint foo (n : nat) :=
  match n with
  | 0 => true
  | S n => g n
  end
with g (n : nat) : bool :=
  match n with
  | 0 => true
  | S n => foo n
  end.
Goal forall n, foo (S n) = g n.
  intros. cbn.
  match goal with
    |- g _ = g _ => reflexivity
  end.
Qed.
