Require Import Setoid.

Parameter X : Set.

Parameter f : X -> X.
Parameter g : X -> X -> X.
Parameter h : nat -> X -> X.

Parameter lem0 : forall x, f (f x) = f x.
Parameter lem1 : forall x, g x x = f x.
Parameter lem2 : forall n x, h (S n) x = g (h n x) (h n x).
Parameter lem3 : forall x, h 0 x = x.

#[export] Hint Rewrite lem0 lem1 lem2 lem3 : rew.

Goal forall x, h 10 x = f x.
Proof.
  intros.
  Time autorewrite with rew. (* 0.586 *)
  reflexivity.
Time Qed. (* 0.53 *)

Goal forall x, h 6 x = f x.
intros.
  Time rewrite_strat topdown lem2.
  Time rewrite_strat topdown lem1.
  Time rewrite_strat topdown lem0.
  Time rewrite_strat topdown lem3.
  reflexivity.
Undo 5.
  Time rewrite_strat topdown (choice lem2 lem1).
  Time rewrite_strat topdown (choice lem0 lem3).
  reflexivity.
Undo 3.
  Time rewrite_strat (topdown (choice lem2 lem1); topdown (choice lem0 lem3)).
  reflexivity.
Undo 2.
  Time rewrite_strat (topdown (choice lem2 (choice lem1 (choice lem0 lem3)))).
  reflexivity.
Undo 2.
  Time rewrite_strat (topdown (choice lem2 (choice lem1 (choice lem0 lem3)))).
  reflexivity.
Undo 2.
  Time rewrite_strat (topdown (choice lem2 lem1 lem0 lem3)).
  reflexivity.
Undo 2.
  Time rewrite_strat fix f := (choice lem2 lem1 lem0 lem3 (progress subterms f) ; try f).
  reflexivity.
Qed.

Goal forall x, h 10 x = f x.
Proof.
  intros.
  Time rewrite_strat topdown (hints rew). (* 0.38 *)
  reflexivity.
Time Qed. (* 0.06 s *)

Set Printing All.
Set Printing Depth 100000.

Tactic Notation "my_rewrite_strat" constr(x) := rewrite_strat topdown x.
Tactic Notation "my_rewrite_strat2" uconstr(x) := rewrite_strat topdown x.
Goal (forall x, S x = 0) -> 1=0.
intro H.
my_rewrite_strat H.
Undo.
my_rewrite_strat2 H.
Abort.
