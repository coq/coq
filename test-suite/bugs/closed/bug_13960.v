Require Ltac2.Ltac2.

Set Default Goal Selector "!".

Ltac2 t () := let _ := Message.print (Message.of_string "hi") in 42.

Goal False.
Proof.
Ltac2 Eval t ().
Abort.
