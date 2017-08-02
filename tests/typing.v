Require Import Ltac2.Ltac2.

(** Ltac2 is typed à la ML. *)

Ltac2 test0 n := Int.add n 1.

Print Ltac2 test0.

Ltac2 test1 () := test0 0.

Print Ltac2 test1.

Fail Ltac2 test2 () := test0 true.

Fail Ltac2 test2 () := test0 0 0.

Ltac2 test3 f x := x, (f x, x).

Print Ltac2 test3.

(** Polymorphism *)

Ltac2 rec list_length l :=
match l with
| [] => 0
| x :: l => Int.add 1 (list_length l)
end.

Print Ltac2 list_length.

(** Pattern-matching *)

Ltac2 ifb b f g := match b with
| true => f ()
| false => g ()
end.

Print Ltac2 ifb.

Ltac2 if_not_found e f g := match e with
| Not_found => f ()
| _ => g ()
end.

Fail Ltac2 ifb' b f g := match b with
| true => f ()
end.

Fail Ltac2 if_not_found' e f g := match e with
| Not_found => f ()
end.

(** Reimplementing 'do'. Return value of the function useless. *)

Ltac2 rec do n tac := match Int.equal n 0 with
| true => ()
| false => tac (); do (Int.sub n 1) tac
end.

Print Ltac2 do.

(** Non-function pure values are OK. *)

Ltac2 tuple0 := ([1; 2], true, (fun () => "yay")).

Print Ltac2 tuple0.

(** Impure values are not. *)

Fail Ltac2 not_a_value := { contents := 0 }.
Fail Ltac2 not_a_value := "nope".
Fail Ltac2 not_a_value := list_length [].
