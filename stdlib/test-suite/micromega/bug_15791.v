From Stdlib Require Import Lia.
Unset Lia Cache.
Set Primitive Projections.

Definition R := nat.
Record S : Set := { regs : R -> nat }.

Record D := { state : Set }.
Definition Z : D := {| state := S |}.
Arguments state d.


Goal forall  (r : R) (s : @state Z), regs s r >= 0.
Proof.
  intros.
  lia.
Qed.
