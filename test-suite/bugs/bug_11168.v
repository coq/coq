Axiom f : forall T, T.
Arguments f &.
Check f _ _.
Check f (_ -> _) _.
Check f (forall x, _) _.
