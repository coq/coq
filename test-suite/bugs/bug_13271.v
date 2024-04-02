Require Import Program.Tactics.
Set Printing Universes.

Local Obligation Tactic := idtac.

Polymorphic Program Definition foo (n m : nat) (H : n = m) : H = H := _.
Solve Obligations with (intros ? ? H; rewrite H; reflexivity).
(* rewrite generates a side effect with a monomorphic universe *)

Polymorphic Program Definition foo' (n m : nat) (H : n = m) : H = H := _.
Next Obligation. intros ? ? H; rewrite H; reflexivity. Qed.
