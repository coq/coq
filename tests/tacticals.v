Require Import Ltac2.Ltac2.

Import Ltac2.Notations.

Goal True.
Proof.
Fail fail.
Fail solve [ () ].
try fail.
repeat fail.
repeat ().
solve [ constructor ].
Qed.

Goal True.
Proof.
first [
  Message.print (Message.of_string "Yay"); fail
| constructor
| Message.print (Message.of_string "I won't be printed")
].
Qed.

Goal True /\ True.
Proof.
Fail split > [ split | |].
split > [split | split].
Qed.

Goal True /\ (True -> True) /\ True.
Proof.
split > [ | split] > [split | .. | split].
intros H; refine &H.
Qed.
