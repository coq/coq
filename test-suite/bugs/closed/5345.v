Ltac break_tuple :=
  match goal with
  | [ H: context[match ?a with | pair n m => _ end] |- _ ] =>
    let n := fresh n in
    let m := fresh m in
    destruct a as [n m]
  end.
