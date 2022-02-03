Fixpoint big n : unit := match n with 0 => tt | S n => match big n with tt => big n end end.

Inductive squash (A : Type) : SProp := Squash : A -> squash A.
Inductive box (A : SProp) : Type := Box : A -> box A.

(* If this is ever unfolded, this will explode *)
Goal Box _ (Squash _ (big 50)) = Box _ (Squash _ tt).
Proof.
reflexivity.
Qed.

Definition SquashC := Squash.

(* If this is ever unfolded, this will explode *)
Goal Box _ (SquashC _ (big 50)) = Box _ (SquashC _ tt).
Proof.
reflexivity.
Qed.
