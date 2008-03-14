(* Test printing of Tactic Notation *)

Tactic Notation "a" constr(x) := apply x.
Tactic Notation "e" constr(x) := exact x.

Lemma test : True -> True /\ True.
intro H; split; [a H|e H].
Show Script.
Qed.

(* Test printing of match context *)
(* Used to fail after translator removal (see bug #1070) *)

Lemma test2 : forall n:nat, forall f: nat -> bool, O = if (f n) then O else O.
Proof.
intros;match goal with |- context [if ?X then _ else _ ] => case X end;trivial.
Show Script.
Qed.
