Axiom p : (nat -> nat) -> nat.
Goal (forall f, p f = f 0) -> forall f, p f = f 0.
Proof. congruence. Qed.

Definition ap {X Y : Type} (f : X -> Y) (x : X) := f x.

Goal (forall f, p f = ap f 0) -> forall f, p f = ap f 0.
Proof. congruence. Qed.

Goal (forall f, p f = ap f (f 0)) -> forall f, p f = ap f (f 0).
Proof. congruence. Qed.

Definition twice (f: nat -> nat) x := f (f x).

Lemma twice_def f x : twice f x = f (f x).
Proof. reflexivity. Qed.

Definition twice_spec f := forall x, twice f x = f (f x).

Goal forall f x, twice f x = f (f x).
Proof.
  intros f x.
  Fail congruence. (* expected, no unfolding *)
  pose proof (H := twice_def).
  congruence.
Qed.
