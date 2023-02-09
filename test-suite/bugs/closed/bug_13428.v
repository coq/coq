Arguments plus : simpl never.

Lemma test1 P : P 3 -> P (1 + 2).
Proof.
intros p3.
simpl.
match goal with |- P (_ + _) => idtac "ok" end.
assumption.
Qed.

Definition plus' := plus.

Lemma test2 P : P 3 -> P (plus' 1 2).
Proof.
intros p3.
simpl.
match goal with |- P (plus' _ _) => idtac "ok" end.
assumption.
Qed.

Lemma test3 P : P 3 -> P (1 + 2).
Proof.
intros p3.
pose (plus'' := plus).
assert (P (plus'' 1 2)).
simpl.
match goal with |- P (plus'' _ _) => idtac "ok" end.
assumption.
assumption.
Qed.

Fixpoint rec_id (x : nat) := match x with O => O | S p => S (rec_id p) end.

Arguments rec_id : simpl never.

Lemma test4 P : P 3 -> P (rec_id 3).
Proof.
intros p3.
simpl.
match goal with |- P (rec_id _) => idtac "ok" end.
assumption.
Qed.

Arguments rec_id ! _ / .
Lemma test5 P : P 3 -> P (rec_id 3).
Proof.
intros p3.
simpl.
match goal with |- P 3 => idtac "ok" end.
assumption.
Qed.
