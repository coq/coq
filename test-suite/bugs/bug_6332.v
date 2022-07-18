Section test.
  Variable (A : Type) (a b : A) (P : A -> Prop).
  Hypothesis H : forall b : A, P b -> P a.
  Hypothesis H' : P b.

  Ltac tac := assert (HH: P b -> P a) by (apply (H b)); clear H; idtac "OK".
  #[local] Hint Extern 1 => tac : core.

  Goal P a.
  Proof.
    auto. (* Prints "OK", solves the goal *)
  Qed.
End test.
