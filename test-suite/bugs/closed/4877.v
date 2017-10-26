Ltac induction_last :=
  let v := match goal with
           | |- forall x y, _ = _ -> _ => 1
           | |- forall x y, _ -> _ = _ -> _ => 2
           | |- forall x y, _ -> _ -> _ = _ -> _ => 3
           end in
  induction v.

Goal forall n m : nat, True -> n = m -> m = n.
  induction_last.
  reflexivity.
Qed.
