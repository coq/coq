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
