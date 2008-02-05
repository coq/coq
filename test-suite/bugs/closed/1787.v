Parameter P : nat -> nat -> Prop.
Parameter Q : nat -> nat -> Prop.
Axiom A : forall x x' x'', P x x' -> Q x'' x' -> P x x''.

Goal (P 1 3) -> (Q 1 3) -> (P 1 1).
intros H H'.
refine ((fun H1 : P 1 _ => let H2 := (_:Q 1 _) in A _ _ _ H1 H2) _).
clear.
Admitted.


