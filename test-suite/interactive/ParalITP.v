Require Import ssreflect.

(* Some boilerplate *)
Fixpoint fib n := match n with
  | O => 1
  | S m => match m with
    | O => 1
    | S o => fib o + fib m end end.

Ltac sleep x n :=
  try (have ? : (fib n = S (fib n)) by reflexivity).

(* Tune that depending on your PC *)
Let time := 18.


(* Beginning of demo *)

Section Demo.

Variable i : True.

Lemma a : True.
Proof using i.
  sleep 1 time.
  idtac.
  sleep 2 time.
  (* Error, jump back to fix it, then Qed again *)
  exact (i i).
Qed.

Lemma b : True.
Proof using i.
  sleep 3 time.
  idtac.
  sleep 4 time.
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
