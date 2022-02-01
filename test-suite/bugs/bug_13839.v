Axiom p: nat -> Prop.

Axiom A: forall (n: id nat), p (1 + n).

Ltac check := match goal with |- id _ => idtac end.

Tactic Notation "test" tactic(tac) := assert_succeeds (unshelve tac; check).

Goal exists n, p n.
  eexists.
  test eapply A. (* ⊢ id nat *)
  test simple eapply A. (* ⊢ nat *)
  test refine (A _). (* ⊢ id nat *)
Abort.

Axiom B: forall (n: id nat), p (S n).

Goal exists n, p n.
  eexists.
  test eapply B. (* ⊢ nat *)
  test simple eapply B. (* ⊢ nat *)
  test refine (B _). (* ⊢ id nat *)
Abort.
