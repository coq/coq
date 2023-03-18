From Ltac2 Require Import Ltac2.
Require Import Ltac2.Message.
Ltac2 msg x := print (of_string x).
Ltac2 y () := msg "msg"; apply I.

Goal True.
y ().
