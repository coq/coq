Require Import Program.

Goal forall (x : Type) (f g : Type -> Type) (H : f x ~= g x), False.
  intros.
  induction H.
Abort.
