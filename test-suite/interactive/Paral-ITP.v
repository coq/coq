Fixpoint fib n := match n with
  | O => 1
  | S m => match m with
    | O => 1
    | S o => fib o + fib m end end.

Ltac sleep n :=
  try (cut (fib n = S (fib n)); reflexivity).

Let time := 18.

Lemma a : True.
Proof.
  sleep time.
  idtac.
  sleep time.
  exact (I I).
Qed.

Lemma b : True.
Proof. 
  do 11 (cut Type; [ intro foo; clear foo | exact Type]).
  sleep time.
  idtac.
  sleep time.
  exact a.
Qed.

Lemma work_here : True.
Proof.
exact I.
