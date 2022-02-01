(* Check effective names of mutual induction schemes *)

Inductive
  even    : nat->Prop :=
    evenO : even  O |
    evenS : forall n, odd n -> even (S n)
with
  odd    : nat->Prop :=
    oddS : forall n, even n -> odd (S n).

Scheme Even_induction := Minimality for even Sort Prop
with   Odd_induction  := Minimality for odd  Sort Prop.

Theorem even_plus_four : forall n:nat, even n -> even (4+n).
Proof.
 intros n H.
 elim H using Even_induction with (P0 := fun n => odd (4+n));
 simpl;repeat constructor;assumption.
Qed.
