(* The following code used to trigger an anomaly in functor substitutions *)

Module Type Foo.

Parameter Inline t : nat.

End Foo.

Module F(X : Foo).

Tactic Notation "foo" ref(x) := idtac.

Ltac g := foo X.t.

End F.

Module N.
Definition t := 0 + 0.
End N.

Module K := F(N).
