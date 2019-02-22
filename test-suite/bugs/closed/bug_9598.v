Module case.

  Inductive pair := K (n1 : nat) (n2 : nat).
  Definition fst (p : pair) : nat := match p with K n _ => n end.

  Definition alias_K a b := K a b.

  Fixpoint rec (x : nat) : nat := fst (K 0 (rec x)).
  Fixpoint rec_ko (x : nat) : nat := fst (alias_K 0 (rec_ko x)).

End case.

Module fixpoint.

  Inductive pair := K (n1 : nat) (n2 : nat).
  Fixpoint fst (p : pair) : nat := match p with K n _ => n end.

  Definition alias_K a b := K a b.

  Fixpoint rec (x : nat) : nat := fst (K 0 (rec x)).
  Fixpoint rec_ko (x : nat) : nat := fst (alias_K 0 (rec_ko x)).

End fixpoint.
