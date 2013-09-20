Goal forall f, f 1 1 -> True.
intros.
match goal with
  | [ H : _ ?a |- _ ] => idtac
end.
Abort.
