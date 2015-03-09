Require Import TestSuite.admit.
Require Setoid.

Parameter f : nat -> nat.
Axiom a : forall n, 0 < n -> f n = 0.
Hint Rewrite a using ( simpl; admit ).

Goal f 1 = 0.
Proof.
  rewrite_strat (topdown (hints core)).
  reflexivity.
Qed.
