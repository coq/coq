From Stdlib Require Import FunInd List.

(* Explanations: This kind of pattern matching displays a legitimate
   unused variable warning in v8.13.

Fixpoint f (l:list nat) : nat :=
  match l with
  | nil => O
  | S n :: nil  => 1
  | x :: l'  => f l'
  end.
*)

(* In v8.13 the same code with "Function" generates a lot more
   warnings about variables created automatically by Function. These
   are not legitimate. PR #13776 (post v8.13) removes all warnings
   about pattern matching variables (and non truly recursive fixpoint)
   for "Function". So this should not generate any warning. Note that
   this PR removes also the legitimate warnings. It would be better if
   this test generate the same warning as the Fixpoint above. This
   test would then need to be updated. *)

(* Ensuring the warning is a warning. *)
Fixpoint f (l:list nat) : nat :=
  match l with
  | nil => O
  | S n :: nil  => 1
  | n :: l'  => f l'
  end.

(* But no warning generated here. *)
Function g (l:list nat) : nat :=
  match l with
  | nil => O
  | S n :: nil  => 1
  | n :: l'  => g l'
  end.
