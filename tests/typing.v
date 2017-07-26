Require Import Ltac2.Ltac2.

(** Ltac2 is typed à la ML. *)

Ltac2 test0 n := Int.add n 1.

Print Ltac2 test0.

Ltac2 test1 () := test0 0.

Print Ltac2 test1.

Fail Ltac2 test2 () := test0 true.

Fail Ltac2 test2 () := test0 0 0.

(** Polymorphism *)

Ltac2 rec list_length l :=
match l with
| [] => 0
| x :: l => Int.add 1 (list_length l)
end.

Print Ltac2 list_length.
