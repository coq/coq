Axioms x y : nat.
Axiom e : x = y.

Obligation Tactic := rewrite e.

Module Type T. End T.

(* we use a functor to ensure side effects are not shared between the tests *)
Module WithQed (X:T).

Program Definition foo (P:forall a, x = a -> Type) : P x eq_refl -> P y e := _.

Next Obligation.
  auto.
Qed.

End WithQed.

Module WithDefined (X:T).

Program Definition foo (P:forall a, x = a -> Type) : P x eq_refl -> P y e := _.

Next Obligation.
  auto.
Defined.

End WithDefined.
