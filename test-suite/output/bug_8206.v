Module Type Sig.
  Parameter add: nat -> nat -> nat.
  Axiom homework: forall (a b: nat), add a b = add b a.
End Sig.

Module Impl.
  Definition add(a b: nat) := plus a b.
  Axiom homework: forall (a b: nat), add 0 b = add b 0.
End Impl.

Module M : Sig := Impl.
