(* In the following code, the (superfluous) lemma [lem] is responsible 
for the failure of congruence. *)

Definition  f : nat -> Prop := fun x => True.

Lemma lem : forall x,  (True -> True)   = ( True ->  f x).
Proof.
  intros. reflexivity.
Qed.

Goal forall  (x:nat), x = x.
Proof.
  intros.
  assert (lem := lem).
  (*clear ax.*)
  congruence.
Qed.

