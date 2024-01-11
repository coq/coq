Definition plus' := plus.

Definition foo := Eval simpl in plus' 1 2.

Arguments plus : simpl never.

Lemma test P : P 3 -> P (plus' 1 2).
Proof.
intros p3.
simpl.
match goal with |- P (plus' 1 2) => idtac end.
(* the order of "Eval simpl" and "Arguments" above resulted in
   incorrect cache and the goal was reduced *)
Abort.
