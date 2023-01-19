Inductive Num : Type :=
| pos :> Pos -> Num
| neg :> Neg -> Num
with Pos : Type :=
| a : Pos
with Neg : Type :=
| b : Neg.

Definition name (x : Num) : nat :=
  match x with
  | a => 0
  | b => 1
  end.

(* Note that the following should be accepted but is not. The reason
   it that it is assumed that the first line is irrefutable so that
   the split on a and b in the first row is dropped. *)

Fail Check fun x y : Num => match x, y with
| x, a => 0
| a, b => 1
| b, b => 2
end.
