(* Test the behaviour of hnf and simpl introduced in revision *)

Parameter n:nat.
Definition a:=0.

Eval simpl in (fix plus (n m : nat) {struct n} : nat :=
  match n with
  | 0 => m
  | S p => S (p + m)
  end) a a.

Eval hnf in match (plus (S n) O) with S n => n | _ => O end.

Eval simpl head in 2 + 2.
Eval cbn head in 2 + 2.
Eval lazy head in 2 + 2.

Eval lazy head delta in 2 + 2.

Eval simpl head in 2 + (2 + 2).

Eval simpl head in (2 + 2) + 2.

Axiom ignore : forall {T}, T -> unit.
Eval simpl head in ignore (fun x => 1 + x).
Eval cbn head in ignore (fun x => 1 + x).
Eval lazy head in ignore (fun x => 1 + x).

Require Import Ltac2.Ltac2.

Ltac2 Eval eval lazy in (2 + 2).
Ltac2 Eval eval lazy head in (2 + 2).
