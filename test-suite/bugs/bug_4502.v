Require Import TestSuite.funind.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Set Strongly Strict Implicit.

Function first_false (n : nat) (f : nat -> bool) : option nat :=
  match n with
  | O => None
  | S m =>
    match first_false m f with
    | (Some _) as s => s
    | None => if f m then None else Some m
    end
  end.
(* undefined universe *)
