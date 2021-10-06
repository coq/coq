Goal forall x, x -> x.
Proof.
  intros.
  match goal with
  | [ |- _ ] => idtac
  (* . From *)
  end.
  assumption.
Qed.
