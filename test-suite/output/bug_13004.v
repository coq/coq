Require Import Ltac2.Ltac2 Ltac2.Message.

Ltac t := ltac2:(print (of_string "hi")).
Ltac u := ident:(H).

Print t.
Print u.
