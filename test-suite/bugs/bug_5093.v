Axiom P : nat -> Prop.
Axiom PS : forall n, P n -> P (S n).
Axiom P0 : P 0.

#[export] Hint Resolve PS : foobar.
#[export] Hint Resolve P0 : foobar.

Goal P 100.
Proof.
Fail typeclasses eauto 100 with foobar.
typeclasses eauto 101 with foobar.
Abort.
