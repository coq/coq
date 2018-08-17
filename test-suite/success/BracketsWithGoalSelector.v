Goal forall A B, B \/ A -> A \/ B.
Proof.
  intros * [HB | HA].
  2: {
    left.
    exact HA.
    Fail right. (* No such goal. Try unfocusing with "}". *)
  }
  Fail 2: { (* Non-existent goal. *)
    idtac. (* The idtac is to get a dot, so that IDEs know to stop there. *)
  1:{ (* Syntactic test: no space before bracket. *)
    right.
    exact HB.
Fail Qed.
  }
Qed.

Lemma foo (n: nat) (P : nat -> Prop):
  P n.
Proof.
  intros.
  refine (nat_ind _ ?[Base] ?[Step] _).
  [Base]: { admit. }
  [Step]: { admit. }
Abort.
