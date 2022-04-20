Module case.

  Inductive pair := K (n1 : nat) (n2 : nat -> nat).
  Definition snd (p : pair) : nat -> nat := match p with K _ f => f end.

  Definition alias_K a b := K a b.

  Fixpoint rec (x : nat) : nat := match x with 0 => 0 | S x => snd (K 0 rec) x end.
  Fixpoint rec_ko (x : nat) : nat := match x with 0 => 0 | S x => snd (alias_K 0 rec_ko) x end.

End case.

Module fixpoint.

  Inductive pair := K (n1 : nat) (n2 : nat -> nat).
  Definition snd (p : pair) : nat -> nat := match p with K _ f => f end.

  Definition alias_K a b := K a b.

  Fixpoint rec (x : nat) : nat := match x with 0 => 0 | S x => snd (K 0 rec) x end.
  Fixpoint rec_ko (x : nat) : nat := match x with 0 => 0 | S x => snd (alias_K 0 rec_ko) x end.

End fixpoint.

Module primproj.

  Set Primitive Projections.

  Inductive pair := K { fst : nat; snd : nat -> nat }.

  Definition alias_K a b := K a b.

  Fixpoint rec (x : nat) : nat := match x with 0 => 0 | S x => snd (K 0 rec) x end.
  Fixpoint rec_ko (x : nat) : nat := match x with 0 => 0 | S x => snd (alias_K 0 rec_ko) x end.

End primproj.
