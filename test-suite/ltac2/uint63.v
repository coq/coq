Require Import Ltac2.Ltac2.
Require Import Ltac2.Uint63.

Ltac2 Eval Control.assert_true (equal (of_int 0) (of_int 0)).

Ltac2 Eval Control.assert_false (equal (of_int 0) (of_int 1)).

Ltac2 Eval Control.assert_true (Int.equal (compare (of_int 0) (of_int 42)) -1).
Ltac2 Eval Control.assert_true (Int.equal (compare (of_int 41) (of_int 41)) 0).
Ltac2 Eval Control.assert_true (Int.equal (compare (of_int 67) (of_int 43)) 1).

Ltac2 Eval Control.assert_true (String.equal (Message.to_string (print (of_int 567))) "567").
