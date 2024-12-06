From Stdlib Require Import Lia Lists.List Program.Wf.

Import ListNotations Nat.

Set Universe Polymorphism.

(* Check that merge_by calls merge_by_func with the identity instance *)

Program Fixpoint merge_by {A : Type} (f : A -> nat) (l0 l1 : list A)
  {measure (length l0 + length l1)} : list A :=
  match l0, l1 with
  | [], _ => l1
  | _, [] => l0
  | n0 :: k0, n1 :: k1 => if f n0 <=? f n1 then
    n0 :: merge_by f k0 l1 else
    n1 :: merge_by f l0 k1
  end.
Next Obligation.
  intros.
  subst;cbn.
  lia.
Qed.
