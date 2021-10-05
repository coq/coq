Fail Fixpoint f n (e : 0 = n) :=
  match 0 as n return (0 = n -> _) with
  | 0 => _
  | S n' => f (n + _) _ _
  end.
