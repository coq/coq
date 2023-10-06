From Coq Require Import Nat.
Fixpoint fac (n : nat) : nat :=
  match n return nat with
  | O | S O => n
  | S n => mult (S n) (fac n)
  end.

From Ltac2 Require Import Ltac2.
Ltac2 red_flags_all : Std.red_flags := {
  Std.rBeta  := true;
  Std.rDelta := true;
  Std.rMatch := true;
  Std.rFix   := true;
  Std.rCofix := true;
  Std.rZeta  := true;
  Std.rConst := []
}.
Optimize Heap.
Instructions Ltac2 Eval
  let t := Std.eval_lazy_whnf red_flags_all '(fac 3) in ().
