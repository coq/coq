Goal 0 = 1.
match goal with
| |- context [?v] =>
  idtac v ; fail
| _ => idtac 2
end.
