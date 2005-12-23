(* Test printing of Tactic Notation *)

Tactic Notation "a" constr(x) := apply x.
Tactic Notation "e" constr(x) := exact x.

Lemma test : True -> True /\ True.
intro H; split; [a H|e H].
Show Script.
Qed.
