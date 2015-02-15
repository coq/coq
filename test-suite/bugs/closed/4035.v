(* Use of dependent destruction from ltac *)
Require Import Program.
Goal nat -> Type.
  intro x.
  lazymatch goal with
  | [ x : nat |- _ ] => dependent destruction x
  end.
