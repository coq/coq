Require Import TestSuite.admit.
(* Test on definitions referring to section variables that are not any
   longer in the current context *)

Section x.

  Hypothesis h : forall(n : nat), n < S n.

  Definition f(n m : nat)(less : n < m) : nat := n + m.

  Lemma a : forall(n : nat), f n (S n) (h n) = 1 + 2 * n.
  Proof.
    (* XXX *) admit.
  Qed.

  Lemma b : forall(n : nat), n < 3 + n.
  Proof.
    clear.
    intros n.
    Fail assert (H := a n).
  Abort.

  Let T := True.
  Definition p := I : T.

  Lemma paradox : False.
  Proof.
    clear.
    set (T := False).
    Fail pose proof p as H.
  Abort.
