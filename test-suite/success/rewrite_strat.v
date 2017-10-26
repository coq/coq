Require Import Setoid. 

Variable X : Set.

Variable f : X -> X.
Variable g : X -> X -> X.
Variable h : nat -> X -> X.

Variable lem0 : forall x, f (f x) = f x.
Variable lem1 : forall x, g x x = f x.
Variable lem2 : forall n x, h (S n) x = g (h n x) (h n x).
Variable lem3 : forall x, h 0 x = x.

Hint Rewrite lem0 lem1 lem2 lem3 : rew.

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
Qed.

Goal forall x, h 10 x = f x.
Proof. 
  intros.
  Time rewrite_strat topdown (hints rew). (* 0.38 *)
  reflexivity.
Time Qed. (* 0.06 s *)

Set Printing All.
Set Printing Depth 100000.
