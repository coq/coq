(* example from bug 5345 *)
Ltac break_tuple :=
  match goal with
  | [ H: context[let '(n, m) := ?a in _] |- _ ] =>
    let n := fresh n in
    let m := fresh m in
    destruct a as [n m]
  end.

(* desugared version of break_tuple *)
Ltac break_tuple' :=
  match goal with
  | [ H: context[match ?a with | pair n m => _ end] |- _ ] =>
    let n := fresh n in
    let m := fresh m in
    idtac
  end.

Ltac multiple_branches :=
  match goal with
  | [ H: match _ with
         | left P => _
         | right Q => _
         end |- _ ] =>
    let P := fresh P in
    let Q := fresh Q in
    idtac
  end.
