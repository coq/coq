Parameter P : forall n : nat, n=n -> Prop.

Goal Prop.
  refine (P _ _).
  2:instantiate (1:=0).
  trivial.
Qed.
