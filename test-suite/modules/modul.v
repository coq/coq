Module M.
  Parameter rel : nat -> nat -> Prop.

  Axiom w : forall n : nat, rel 0 (S n).

  Hint Resolve w.

  (* <Warning> : Grammar is replaced by Notation *)

  Print Hint *.

  Lemma w1 : rel 0 1.
  auto.
  Qed.

End M.

Locate Module M.

(*Lemma w1 : (M.rel O (S O)).
Auto.
*)

Import M.

Lemma w1 : rel 0 1.
auto.
Qed.

Check (rel 0 0).
Locate rel.

Locate Module M.

Module N := Top.M.
