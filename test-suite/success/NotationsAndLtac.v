(* Test that adding notations that overlap with the tactic grammar does not
* interfere with Ltac parsing. *)

Module test1.
  Notation "x [ y ]" := (fst (id x, id y)) (at level 11).

  Goal True \/ (exists x : nat, True /\ True) -> True.
  Proof.
  intros [|[a [y z]]]; [idtac|idtac]; try solve [eauto | trivial; [trivial]].
  Qed.
End test1.

Module test2.
  Notation "x [ y ]" := (fst (id x, id y)) (at level 100).
  Goal True \/ (exists x : nat, True /\ True) -> True.
  Proof.
  intros [|[a [y z]]]; [idtac|idtac]; try solve [eauto | trivial; [trivial]].
  Qed.
End test2.

Module test3.
  Notation "x [ y ]" := (fst (id x, id y)) (at level 1).
  Goal True \/ (exists x : nat, True /\ True) -> True.
  Proof.
  intros [|[a [y z]]]; [idtac|idtac]; try solve [eauto | trivial; [trivial]].
  Qed.
End test3.

Module test1'.
  Notation "x [ [ y ] ] " := (fst (id x, id y)) (at level 11).

  Goal True \/ (exists x : nat, True /\ True) -> True.
  Proof.
  intros [|[a [y z]]]; [idtac|idtac]; try solve [eauto | trivial; [trivial]].
  Qed.
End test1'.

Module test2'.
  Notation "x [ [ y ] ]" := (fst (id x, id y)) (at level 100).
  Goal True \/ (exists x : nat, True /\ True) -> True.
  Proof.
  intros [|[a [y z]]]; [idtac|idtac]; try solve [eauto | trivial; [trivial]].
  Qed.
End test2'.

Module test3'.
  Notation "x [ [ y ] ]" := (fst (id x, id y)) (at level 1).
  Goal True \/ (exists x : nat, True /\ True) -> True.
  Proof.
  intros [|[a [y z]]]; [idtac|idtac]; try solve [eauto | trivial; [trivial]].
  Qed.
End test3'.
