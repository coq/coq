Parameter P : forall n : nat, n=n -> Prop.

Goal Prop.
  refine (P _ _).
    instantiate (1:=0).
  trivial.
Qed.
