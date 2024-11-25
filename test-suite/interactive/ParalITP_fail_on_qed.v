(* Some boilerplate *)
Fixpoint fib n := match n with
  | O => 1
  | S m => match m with
    | O => 1
    | S o => fib o + fib m end end.

Ltac sleep n :=
  try (cut (fib n = S (fib n)); reflexivity).

(* Tune that depending on your PC *)
Let time := 10.


(* Beginning of demo *)

Section Demo.

Variable i : True.

Lemma a (n : nat) : nat.
Proof using.
  revert n.
  fix f 1.
  apply f.
Qed.

Lemma b : True.
Proof using i.
  sleep time.
  idtac.
  sleep time.
  (* Here we use "a" *)
  exact I.
Qed.

Lemma work_here : True /\ True.
Proof using i.
(* Jump directly here, Coq reacts immediately *)
split.
  exact b.  (* We can use the lemmas above *)
exact I.
Qed.

End Demo.

From Corelib Require Import Program.Tactics.
Obligation Tactic := idtac.
Program Definition foo : nat -> nat * nat :=
  fix f (n : nat) := (0,_).

Next Obligation.
intros f n; apply (f n).
Qed.
