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

(* Was
Anomaly: Uncaught exception Not_found. Please report. *)
