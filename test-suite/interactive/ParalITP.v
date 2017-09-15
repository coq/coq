(* Some boilerplate *)
Fixpoint fib n := match n with
  | O => 1
  | S m => match m with
    | O => 1
    | S o => fib o + fib m end end.

Ltac sleep n :=
  try (cut (fib n = S (fib n)); reflexivity).

(* Tune that depending on your PC *)
Let time := 18.


(* Beginning of demo *)

Section Demo.

Variable i : True.

Lemma a : True.
Proof using i.
  sleep time.
  idtac.
  sleep time.
  (* Error, jump back to fix it, then Qed again *)
  exact (i i).
Qed.

Lemma b : True.
Proof using i. 
  sleep time.
  idtac.
  sleep time.
  (* Here we use "a" *)
  exact a.
Qed.

Lemma work_here : True /\ True.
Proof using i.
(* Jump directly here, Coq reacts immediately *)
split.
  exact b.  (* We can use the lemmas above *)
exact a.
Qed.

End Demo.
