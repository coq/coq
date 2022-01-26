Axiom word : nat -> Set.
Axiom wones : forall (sz : nat), word sz.

Axiom combine : forall (sz1 : nat) (w : word sz1), forall sz2, word sz2 -> word (sz1 + sz2).
Axiom split1 : forall (sz1 sz2 : nat), word (sz1 + sz2) -> word sz1.
Axiom bitwp : forall (f : bool -> bool -> bool) sz (w1 : word sz), word sz -> word sz.
Axiom split1_combine : forall sz1 sz2 (w : word sz1) (z : word sz2), split1 sz1 sz2 (combine _ w _ z) = w.

Theorem wnot_split1 : forall sz1 sz2 w w', w' = split1 sz1 sz2 (bitwp xorb _ (wones (sz1 + sz2)) w).
Proof.
intros.
erewrite <- split1_combine with (w := wones _).
Abort.
